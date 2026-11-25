import LojitaCtx.Posix.Stream

namespace LojitaCtx.Io
open LojitaCtx.Posix

abbrev lf : UInt8 := 10

/-- Incremental framing of the bytes already returned by the descriptor.
Both accumulators are reversed so every input byte is processed once. -/
structure Framing where
  completeRev : List Bytes := []
  tailRev : Bytes := []

def Framing.byte (s : Framing) (b : UInt8) : Framing :=
  if b = lf then ⟨(b :: s.tailRev).reverse :: s.completeRev, []⟩
  else { s with tailRev := b :: s.tailRev }

def Framing.chunk (s : Framing) (bs : Bytes) : Framing := bs.foldl Framing.byte s
def Framing.lines (s : Framing) : List Bytes :=
  s.completeRev.reverse ++ (if s.tailRev.isEmpty then [] else [s.tailRev.reverse])

@[simp] theorem chunk_append (s : Framing) (xs ys : Bytes) :
    s.chunk (xs ++ ys) = (s.chunk xs).chunk ys := List.foldl_append

theorem chunk_without_lf (s : Framing) (xs : Bytes) (h : lf ∉ xs) :
    s.chunk xs = ⟨s.completeRev, xs.reverse ++ s.tailRev⟩ := by
  induction xs generalizing s with
  | nil => simp [Framing.chunk]
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    change (s.byte x).chunk xs = _
    rw [ih _ h.2]
    have hx : x ≠ lf := Ne.symm h.1
    simp [Framing.byte, hx, List.append_assoc]

structure BufReader where
  fd : Fd
  chunkSize : Nat := 65536
  buf : ByteArray := ByteArray.empty
  pos : Nat := 0
  ready : List Bytes := []
  eof : Bool := false

def BufReader.frame (r : BufReader) : Framing :=
  ⟨r.ready.reverse, (r.buf.data.toList.drop r.pos).reverse⟩

def BufReader.withFrame (r : BufReader) (f : Framing) : BufReader :=
  { r with buf := f.tailRev.reverse.toByteArray, pos := 0, ready := f.completeRev.reverse }

@[simp] theorem frame_withFrame (r : BufReader) (f : Framing) :
    (r.withFrame f).frame = f := by
  cases f
  simp [-List.data_toByteArray, List.toList_data_toByteArray, BufReader.withFrame, BufReader.frame]

def BufReader.pending (r : BufReader) : Bytes := r.ready.flatten ++ r.buf.data.toList.drop r.pos

def BufReader.ingest (r : BufReader) (bs : Bytes) : BufReader := r.withFrame (r.frame.chunk bs)

def BufReader.clear (r : BufReader) : BufReader := r.withFrame {}

inductive ReadMode where
  | line | all | exact (count : Nat)
  deriving Inhabited

abbrev ReadResult := Ret (Option Bytes) × BufReader

/-- A missing result means that precisely one further read is needed. -/
def BufReader.inspect (r : BufReader) : ReadMode → Option ReadResult
  | .line =>
    match r.ready with
    | line :: rest => some (.ok (some line), {r with ready := rest})
    | [] =>
      if r.eof then
        let bs := r.buf.data.toList.drop r.pos
        some (.ok (if bs.isEmpty then none else some bs), r.clear)
      else none
  | .all => if r.eof then some (.ok (some r.pending), r.clear) else none
  | .exact n =>
    let bs := r.pending
    if n ≤ bs.length then
      some (.ok (some (bs.take n)), r.clear.ingest (bs.drop n))
    else if r.eof then some (.err .EIO, r) else none

inductive ReadProgress where
  | ready (r : BufReader)
  | stopped (result : ReadResult)

def BufReader.receive (r : BufReader) : Ret Bytes → ReadProgress
  | .ok []     => .ready { r with eof := true }
  | .ok (b::bs) => .ready (r.ingest (b::bs))
  | .err .EINTR => .ready r
  | .err e => .stopped (.err e, r)
  | .wouldBlock w => .stopped (.wouldBlock w, r)

/-- Properly delimited lines may be fragmented arbitrarily before temporary
starvation. The suffix stops at its first newline, as in Linux userspace. -/
theorem bufReader_halfline_lossless (fd : Fd) (pre post : Bytes)
    (hpre : lf ∉ pre) (hpost : lf ∉ post) (pipe : StreamBuf)
    (empty : pipe.pendingBytes = []) (openWriter : pipe.writers ≠ 0) :
    let r := (BufReader.mk fd 4096 ByteArray.empty 0 [] false).ingest pre
    r.inspect .line = none ∧
    r.receive (streamRead canonicalSlice true pipe).1 = .stopped (.err .EAGAIN, r) ∧
    ∃ r', (r.ingest (post ++ [lf])).inspect .line =
      some (.ok (some (pre ++ post ++ [lf])), r') := by
  have blocked : (streamRead canonicalSlice true pipe).1 = .err .EAGAIN := by
    simp [streamRead, canonicalSlice, empty, openWriter]
    rfl
  simp only [blocked, BufReader.ingest, chunk_append]
  simp only [chunk_without_lf _ pre hpre, chunk_without_lf _ post hpost]
  simp [-List.data_toByteArray, List.toList_data_toByteArray, BufReader.frame, BufReader.withFrame,
    BufReader.inspect, BufReader.receive, Framing.chunk, Framing.byte, List.append_assoc]

end LojitaCtx.Io
