# Lean 4.36 的 ByteArray 与 G1 纯度实验

对最小类型 `Payload.reg (data : ByteArray)`，可以保留公开类型和构造器，在原 G1 的声明依赖遍历中消除全部 6 个命中，并保持本实验所测的原生 ABI 行为。项目级 G1 仍然失败。编译器为实现这些行为而选取的替换函数也依赖原生操作。

## 47 服务器实测

以下工具链对照均使用同一个 Lojita 提交 `9225b46e02ca913a3f6a020c7ee5ece8ed2efe57`，从干净检出运行原版 `./test-g1-purity-and-size.sh`。每组均检查 2,925 个声明。前三组各有 8,577 个可达常量，最后一组有 8,573 个。项目门禁均退出 1。

| 工具链 | 最小载荷违规 / 可达 | UInt8 | Array、ByteArray、Payload（各自） | Nat 算术 | 项目 G1 违规 |
| --- | --- | --- | --- | --- | --- |
| 官方 Lean 4.36.0 | 6 / 63 | 256 / 256 | 257 / 257 | 1,333 / 1,333 | 101（83 extern、17 unsafe、1 公理） |
| 移除六个 extern | 0 / 63 | 1 / 256 | 0 / 257 | 3 秒超时 | 95（77 extern、17 unsafe、1 公理） |
| 再加入原生适配 | 0 / 63 | 256 / 256 | 257 / 257 | 1,333 / 1,333 | 95（77 extern、17 unsafe、1 公理） |
| 再改用安全的构造器编号 | 0 / 63 | 256 / 256 | 257 / 257 | 1,333 / 1,333 | 91（77 extern、13 unsafe、1 公理） |

六个命中是 `Nat.add`、`Nat.mul`、`Nat.pow`、`UInt8.ofBitVec`、`Array.mk` 和 `ByteArray.mk`。每组均通过三个构造器的 Lean 投影等式证明。原生测试从 C 调用编译后的 Lean 函数，检查所有单字节值，以及长度 0 至 256 的普通数组、紧凑字节数组和载荷的运行时表示、长度和逐字节内容。算术覆盖小整数加、乘、幂及其组合，另测了跨越小整数表示边界和 42 位十进制数的加法。

## 适配及其边界

`prelude.patch` 移除六个声明的 extern 属性，并将匹配自然数所需的相等判定和减法相关定义移到首次使用之前。单独应用它会导致字节构造器丢失正确的原生表示。原生编译还会把 `Nat.succ` 降为加一，使按递归定义生成的加法再次调用自身。

`Packing.lean` 为三个构造器提供有等式证明的编译器替换，分别通过数组追加、字节数组追加和 `UInt8.ofNat` 产生运行时表示。`successor.patch` 让编译器通过 `Nat.abiSucc` 调用运行时的 `lean_nat_succ`。客户端照常导入 `Init`。链接映射和符号表可用于核对测试 ELF 采用的本地算术定义。

原 G1 遍历声明依赖及 `implemented_by`，不跟踪本实验使用的 `csimp` 替换。因此另用 `Audit.lean` 查询四个实际生效的替换，并用同样的违规判定审计其实现。292 个可达常量中有 17 个命中，包括 `Nat.abiSucc`、`Array.push`、`ByteArray.push` 和 `UInt8.ofNat`。两次审计的起点不同，17 和项目的 95 不能相加。

实验仅重编相应的 Prelude、Init 模块和测试程序，链接时显式加入生成的对象文件，并继续使用官方共享运行时及其余预编译标准库。上述四组对照验证原生用例和项目 G1。下节另外验证默认项目链接与启动。实验未执行完整工具链自举或 PB 任务。

## 四种构造器的原生编号

`tags.patch` 将 `Bool.ctorIdx`、`Option.ctorIdx`、`List.ctorIdx` 和 `Except.ctorIdx` 定义为对输入的 Lean 分支匹配。四个函数仍保留原有名称、类型和编号语义。每个函数单独审计均为零命中，生成的 Prelude C 中均已消除原来的 unsafe 实现。原生测试覆盖布尔值、空构造器、含小整数和堆上大整数的构造器，14 项检查通过。直接调用布尔的标量及装箱入口也通过了 4 项检查。

在 `adapted` 和 `pure-tags` 两组间，规格必需的 `String` 类型的声明闭包从 21 个命中降至 19 个，四个既有编译替换的实现闭包从 17 个降至 15 个。后者仍有 `Nat.abiSucc`、`ByteArray.push` 等原生依赖。完整项目中的其他类型仍会用到 `getObjTagNat`。

## 从干净源码启动修复后的 Lojita

同一应用源码 `561e94d` 在 47 服务器的结果如下。编译审计同时遍历已注册的 `csimp` 替换实现和等式证明。

| 工具链 | 原规则命中 | 含编译替换和证明的命中 | 原生验证 |
| --- | ---: | ---: | --- |
| 官方 Lean | 91 | 109 | 项目 G2–G5 通过 |
| 官方算术与打包，只改四种构造器编号 | 87 | 105 | 重新构建静态 Init 归档后，默认 Lake 构建、新产物 20 次独立启动均通过 `verify-self`，项目 G2–G5 通过 |
| 字节数组与自然数适配 | 85 | 104 | 独立 ABI 和算术样本通过 |
| 字节数组、自然数和四种编号均适配 | 81 | 100 | 独立 ABI 和算术样本通过 |

要验证第二行的默认链接，可以在本分支直接运行：

```sh
./experiments/g1-toolchain/build-native-tags.sh
```

脚本在新目录内替换私有的 `libInit.a`，用当前提交构建 Lojita，再运行新生成的 `.lake/build/bin/lojita verify-self`。标准工具链安装不参与写入。

在包含原始算术适配与 Bool 修复的单独对照中，`install-init-archive.sh STAGE RELEASE --packing` 还重建了 Init 导入根和打包模块，并为旧库保留的装箱 UInt8 入口提供转接。它通过了 256 个值的 ABI 对照，也使默认构建链接成功。该版本运行 `verify-self` 时退出 134，采样栈显示连续的 `l_Nat_add` 递归调用。小输入的 1,333 项算术测试无法发现这一启动失败。

## 复现

在 Linux x86-64 的该分支检出中，将官方 Lean 4.36.0 的 bin 目录加入 PATH，准备 Bash、Python 3、Git、GNU C 工具链、patch、tar 和 coreutils。脚本检查工具链提交和 Prelude 源码哈希。可直接运行，也可传入一个尚不存在的输出目录。

```sh
./experiments/g1-toolchain/run.sh
```

脚本首行输出实验目录。四个子目录 `official/`、`stripped/`、`adapted/`、`pure-tags/` 各自保留 `audit.log`、`abi.log`、`arithmetic.log`、`tags.log`、`check.map`、原生可执行文件 `check` 和完整的 `project-g1.log`。超时时算术日志可能为空，可在控制台记录中查看退出码 124。脚本退出 0 表示复现了四组预期观测，其中包括项目 G1 的四次失败。

## 有证的有界算术实验

在四标签工具链的原生混合归档中，按第二个参数逐个取后继的 `Nat.add` 会用尽线程栈。`Arithmetic.lean` 保留 Prelude 中的逻辑定义，用 `@[csimp]` 注册三个经过 Lean 检查的等式。加法取两数较大者的两倍作为上界，通过三次自然数减法得到和。乘法和幂按二进制位迭代。每轮的剩余乘数或指数都减半，生成的 C 使用循环。

在上文的 `run.sh` 生成 `pure-tags/` 后运行下列命令。两个输出目录均应事先不存在。第一条验证算术组件，第二条诊断当前分支的完整 Lojita 启动，任一次失败都会使诊断返回非零。

```sh
./experiments/g1-toolchain/bounded-arithmetic.sh /path/to/pure-tags /tmp/g1-bounded
./experiments/g1-toolchain/bounded-smoke.sh /tmp/g1-bounded /tmp/g1-bounded-sdk
```

`bounded-arithmetic.sh` 编译注册规则前后的两份相同原生调用程序。旧调用点保留 `l_Nat_add/mul/pow` 三个符号，各个符号的实现直接转到对应的 `l_G1Arithmetic_add/mul/pow`。脚本检查两个借用参数、拥有所有权的返回值以及生成 C 的运行时调用。新编译的程序直接使用 Lean 的编译器等式。两套程序各通过 1333 个算术样例、11 组 Python 任意精度整数对照、构造器 ABI 和 14 个标签检查。大数样例覆盖 2000 位十进制的进位、2048 位乘 3072 位以及 2 的 16384 次幂。

`audit.log` 分别列出原声明、替换体和等式证明的联合依赖闭包。四标签配置下，加法闭包含 6 个 `extern`，乘法与幂各含 11 个。生成 C 的数值原语是 `lean_nat_dec_eq`、`lean_nat_dec_le`、`lean_nat_mod`、`lean_nat_shiftl`、`lean_nat_shiftr` 和 `lean_nat_sub`。代码还使用 Lean 装箱、引用计数和模块初始化。项目 strict G1 仍要求整个可达闭包内的禁止项均为零。

47 服务器上，单独替换 Bool 标签的混合库在默认 ASLR 下原先因加法栈溢出退出 134。换入有界算术后，旧构建重复 12 次成功 1 次。用工具链 Clang 重编后，10 次成功 1 次。四标签配置从干净项目构建完成 370 项，默认 ASLR 下重复启动 `verify-self` 12 次，其中 1 次成功，11 次收到 SIGSEGV。在单 Bool 配置下保留 ASLR 的 GDB 回溯显示，崩溃经过 `Lean.CollectAxioms.collect`、`Lean.mkModuleData` 和 `lean_alloc_small_object_core`。该回溯尚未确定损坏内存的起点。在本轮修复后的应用源码 `561e94d` 上也确认了这一问题。默认 Lake 构建完成 373 项，但 12 次独立 `verify-self` 全部收到 SIGSEGV。该配置的原规则命中为 81，计入编译替换及证明则为 101。完整混合 SDK 仍未通过可靠启动验证。
