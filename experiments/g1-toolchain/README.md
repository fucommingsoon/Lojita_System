# Lean 4.36 的 ByteArray 与 G1 纯度实验

对最小类型 `Payload.reg (data : ByteArray)`，可以保留公开类型和构造器，在原 G1 的声明依赖遍历中消除全部 6 个命中，并保持本实验所测的原生 ABI 行为。项目级 G1 仍然失败。编译器为实现这些行为而选取的替换函数也依赖原生操作。

## 47 服务器实测

每组使用同一个 Lojita 提交 `9225b46e02ca913a3f6a020c7ee5ece8ed2efe57`，从干净检出运行原版 `./test-g1-purity-and-size.sh`。三个项目运行各检查 2,925 个声明、8,577 个可达常量，退出码均为 1。

| 工具链 | 最小载荷违规 / 可达 | UInt8 | Array、ByteArray、Payload（各自） | Nat 算术 | 项目 G1 违规 |
| --- | --- | --- | --- | --- | --- |
| 官方 Lean 4.36.0 | 6 / 63 | 256 / 256 | 257 / 257 | 1,333 / 1,333 | 101（83 extern、17 unsafe、1 公理） |
| 移除六个 extern | 0 / 63 | 1 / 256 | 0 / 257 | 3 秒超时 | 95（77 extern、17 unsafe、1 公理） |
| 再加入原生适配 | 0 / 63 | 256 / 256 | 257 / 257 | 1,333 / 1,333 | 95（77 extern、17 unsafe、1 公理） |

六个命中是 `Nat.add`、`Nat.mul`、`Nat.pow`、`UInt8.ofBitVec`、`Array.mk` 和 `ByteArray.mk`。每组均通过三个构造器的 Lean 投影等式证明。原生测试从 C 调用编译后的 Lean 函数，检查所有单字节值，以及长度 0 至 256 的普通数组、紧凑字节数组和载荷的运行时表示、长度和逐字节内容。算术覆盖小整数加、乘、幂及其组合，另测了跨越小整数表示边界和 42 位十进制数的加法。

## 适配及其边界

`prelude.patch` 移除六个声明的 extern 属性，并将匹配自然数所需的相等判定和减法相关定义移到首次使用之前。单独应用它会导致字节构造器丢失正确的原生表示。原生编译还会把 `Nat.succ` 降为加一，使按递归定义生成的加法再次调用自身。

`Packing.lean` 为三个构造器提供有等式证明的编译器替换，分别通过数组追加、字节数组追加和 `UInt8.ofNat` 产生运行时表示。`successor.patch` 让编译器通过 `Nat.abiSucc` 调用运行时的 `lean_nat_succ`。客户端照常导入 `Init`。链接映射和符号表可用于核对测试 ELF 采用的本地算术定义。

原 G1 遍历声明依赖及 `implemented_by`，不跟踪本实验使用的 `csimp` 替换。因此另用 `Audit.lean` 查询四个实际生效的替换，并用同样的违规判定审计其实现。292 个可达常量中有 17 个命中，包括 `Nat.abiSucc`、`Array.push`、`ByteArray.push` 和 `UInt8.ofNat`。两次审计的起点不同，17 和项目的 95 不能相加。

实验仅重编相应的 Prelude、Init 模块和测试程序，链接时显式加入生成的对象文件，并继续使用官方共享运行时及其余预编译标准库。验证范围限于上述原生用例和项目 G1，未检验完整工具链自举、任意 Lake 应用的默认链接、PB 任务或性能。

## 复现

在 Linux x86-64 的该分支检出中，将官方 Lean 4.36.0 的 bin 目录加入 PATH，准备 Bash、Python 3、Git、GNU C 工具链、patch、tar 和 coreutils。脚本检查工具链提交和 Prelude 源码哈希。可直接运行，也可传入一个尚不存在的输出目录。

```sh
./experiments/g1-toolchain/run.sh
```

脚本首行输出实验目录。三个子目录 `official/`、`stripped/`、`adapted/` 各自保留 `audit.log`、`abi.log`、`arithmetic.log`、`check.map`、原生可执行文件 `check` 和完整的 `project-g1.log`。超时时算术日志可能为空，可在控制台记录中查看退出码 124。脚本退出 0 表示复现了三组预期观测，其中包括项目 G1 的三次失败。
