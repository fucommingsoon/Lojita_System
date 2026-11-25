import LojitaCtx.Io.Confluence

namespace LojitaCtx.Io
open LojitaCtx.Posix

/-- The first actual readLine returns EAGAIN without discarding its unterminated
    line. The same returned reader consumes the resumed pipe and returns the
    joined line. The stream reads here use adequate positive request sizes. -/
theorem readLine_halfline_syscalls {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fd : Fd)
    (pre post : Bytes) (noLF₀ : lf ∉ pre) (noLF₁ : lf ∉ post) (pipe : StreamBuf)
    (empty : pipe.pendingBytes = []) (openEnd : pipe.writers ≠ 0) :
    let r₀ : BufReader := {fd,chunkSize := max 1 (max pre.length (post.length+1))}
    let r := r₀.ingest pre
    let a := (streamRead canonicalSlice true pipe).1
    let resumed := {pipe with pendingBytes := post ++ [lf]}
    let b := (streamRead {maxBytes := post.length+1} true resumed).1
    Finishes ((readLine cap r).observe 1) (readAnswers [a]) (.err .EAGAIN,r) ∧
    ∃ final, Finishes ((readLine cap r).observe 1) (readAnswers [b])
      (.ok (some (pre ++ post ++ [lf])),final) := by
  intro r₀ r a resumed b
  have noneReady : r.inspect .line = none := by
    simp [r,r₀,BufReader.ingest,chunk_without_lf _ pre noLF₀,BufReader.frame,BufReader.withFrame,BufReader.inspect]
  have first : a = .err .EAGAIN := by
    simp [a,streamRead,canonicalSlice,empty,openEnd]; rfl
  have second : b = .ok (post ++ [lf]) := by
    cases post with
    | nil => rfl
    | cons x xs =>
      simp [b,resumed,streamRead]
      exact List.take_of_length_le (by simp)
  have found : ∃ final, (r.ingest (post ++ [lf])).inspect .line =
      some (.ok (some (pre ++ post ++ [lf])),final) := by
    simp only [r,r₀,BufReader.ingest,chunk_append]
    simp only [chunk_without_lf _ pre noLF₀,chunk_without_lf _ post noLF₁]
    simp [-List.data_toByteArray, List.toList_data_toByteArray, BufReader.frame, BufReader.withFrame,
      BufReader.inspect, Framing.chunk, Framing.byte, List.append_assoc]
  obtain ⟨final,found⟩ := found
  have ask : (readLine cap r).observe 1 = .ask (.read r.fd (max 1 r.chunkSize)) cap
      (fun reply => PosixProg.unfoldPrefix (readStep cap .line) 0 (r.receive reply)) := by
    change PosixProg.unfoldPrefix (readStep cap .line) 1 (.ready r) = _
    rw [PosixProg.unfoldPrefix]
    simp only [readStep,noneReady]
  rw [ask,first,second]
  constructor
  · exact .ask (.done _)
  · refine ⟨final,.ask ?_⟩
    have positive : post ++ [lf] ≠ [] := by simp
    cases eqn : post ++ [lf] with
    | nil => exact False.elim (positive eqn)
    | cons x xs =>
      rw [eqn] at found
      change Finishes (PosixProg.unfoldPrefix (readStep cap .line) 0 (.ready (r.ingest (x::xs)))) [] _
      rw [PosixProg.unfoldPrefix]
      simp only [readStep,found]
      exact .done _

end LojitaCtx.Io
