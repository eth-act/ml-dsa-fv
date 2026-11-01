rows=[l.rstrip('\n').split('\t') for l in open('MlDsaOpt44/listing.tsv')][1:]
pc=lambda i:int(rows[i][1])
vals=open('MlDsaOpt44/Main/Wp11Gen/tblv.txt').read()
out=[]
out.append('''import MlDsaOpt44.Main.Base
set_option warningAsError true
/-! # Segment `1085 … 3068`: the 248 NTT zeta records (straight line).

Eight blocks of 31 `PUSH3 v; PUSH2 TBL + 32 i; MSTORE` records. Block `k`
stores chunk `k` (`tblChunk`); `tblMem m k` is the memory after `k` blocks. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The record words as pushed by the code. -/
def tblv (i : Nat) : Nat := [''' + vals + '''].getD i 0

theorem tblv_eq : ∀ i, i < 248 → tblv i = nttRec i := by decide +kernel

theorem tblv_lt : ∀ i, i < 248 → tblv i < 2 ^ 256 := by decide +kernel

/-- Block `k`'s 31 stores on top of `M`. -/
def tblChunk (M : ByteArray) (k : Nat) : ByteArray :=
  storeWords M (TBL + 992 * k) (fun i => tblv (31 * k + i)) 31

/-- Memory after the first `k` blocks. -/
def tblMem (m : ByteArray) : Nat → ByteArray
  | 0 => m
  | k + 1 => tblChunk (tblMem m k) k

theorem tblMem_frame (m : ByteArray) : ∀ k, FrameExcept m (tblMem m k) [(TBL, TBL + 992 * k)]
  | 0 => FrameExcept.refl _ _
  | k + 1 => by
    show FrameExcept m (tblChunk (tblMem m k) k) _
    unfold tblChunk
    apply FrameExcept.mono ((tblMem_frame m k).trans
      (FrameExcept.storeWords (tblMem m k) (TBL + 992 * k) (fun i => tblv (31 * k + i)) 31))
    intro r hr
    refine ⟨(TBL, TBL + 992 * (k + 1)), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

theorem word_tblMem (m : ByteArray) : ∀ k, k ≤ 8 → ∀ i, i < 31 * k →
    word (tblMem m k) (TBL + 32 * i) = tblv i
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, hk, i, hi => by
    simp only [tblMem, tblChunk]
    by_cases h : 31 * k ≤ i
    · have := word_storeWords (m := tblMem m k) (base := TBL + 992 * k)
        (v := fun i => tblv (31 * k + i)) (i := i - 31 * k) (tblv_lt _ (by omega)) 31 (by omega)
      rw [show TBL + 992 * k + 32 * (i - 31 * k) = TBL + 32 * i by omega,
        show 31 * k + (i - 31 * k) = i by omega] at this
      exact this
    · rw [FrameExcept.word (FrameExcept.storeWords _ _ _ 31) (by
        simp only [avoids_cons, avoids_nil, and_true]; omega)]
      exact word_tblMem m k (by omega) i (by omega)
''')
for k in range(8):
    a=220+93*k; b=a+93
    idx=', '.join(str(i) for i in range(a,b))
    out.append(f'''
theorem tbl_b{k} {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s {pc(a)} [flag b] M) (callState s {pc(b)} [flag b] (tblChunk M {k})) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2065 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [{idx}]
  rfl
''')
chain='(tbl_b0 hs b m)'
for k in range(1,8):
    chain=f'({chain}.trans (tbl_b{k} hs b _))'
out.append(f'''
theorem seg_tbl_proof {{s : State}} (hs : Ctx s) {{cd m : ByteArray}} (hI : Inv1 cd m) (b : Bool) :
    ∃ m', Inv2 cd m' ∧
      Reach (callState s 1085 [flag b] m) (callState s 3068 [flag b] m') Gas.pTbl := by
  have hfr : FrameExcept m (tblMem m 8) [(TBL, TBL + 7936)] := tblMem_frame m 8
  refine ⟨tblMem m 8,
    ⟨hI.rc4.frame hfr (by avoids_tac), hI.rc1.frame hfr (by avoids_tac), fun i hi => ?_,
      hI.z.frame hfr (by avoids_tac), hI.hp.frame hfr (by avoids_tac),
      (hI.zLow.mono (by unfold MISC; omega) (by unfold TBL ZH; omega)).frame hfr (by avoids_tac),
      (hI.zLow.mono (by unfold MISC CW; omega) (by unfold ABUF ZH; omega)).frame hfr (by avoids_tac),
      hI.zHigh.frame hfr (by avoids_tac)⟩, ?_⟩
  · rw [word_tblMem m 8 le_rfl i (by omega), tblv_eq i hi]
  · exact {chain}.mono (by unfold Gas.pTbl; omega)

end MlDsaOpt44.Proofs
''')
open('MlDsaOpt44/Main/Tbl/Blocks.lean','w').write(''.join(out))
