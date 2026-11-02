import MlDsaOptGlam44.Layout
set_option warningAsError true
/-! # The 240 records of the 4 + 4 NTT's table, segment `99 … 2018`

`tblv` (the pushed record words, `tblv_eq`: they are `nttRecG`), `tblChunk`
(block `k`'s 30 stores) and `tblMem` (memory after `k` blocks): the v4
module (`MlDsaOpt44/Main/Tbl/Defs.lean`) for this artifact's table. -/

namespace MlDsaOptGlam44.Proofs

open MlDsaOpt44.Proofs (TBL)

open MlDsaOptCommon

/-- The record words as pushed by the code. -/
def tblv (i : Nat) : Nat := [2725464, 2706023, 95776, 4450022, 6851714, 4702672, 5339162, 2091667, 3407706, 2316500, 3817976, 5037939, 2244091, 5933984, 4817955, 1024112, 3077325, 3530437, 6927966, 3475950, 2176455, 6795196, 266997, 2434439, 7144689, 3513181, 4860065, 4621053, 7183191, 5187039, 7300517, 6718724, 4788269, 7122806, 1939314, 4296819, 7380215, 900702, 1859098, 909542, 819034, 495491, 6767243, 8337157, 7857917, 3585928, 5842901, 3915439, 5190273, 5223087, 4747489, 126922, 7725090, 5257975, 2031748, 3207046, 4823422, 7855319, 7611795, 4784579, 7830929, 4519302, 5336701, 3412210, 7396998, 2147896, 2715295, 342297, 286988, 5942594, 4108315, 3437287, 5038140, 1735879, 203044, 7260833, 3574422, 5512770, 5412772, 4686924, 7969390, 5903370, 2842341, 2691481, 5790267, 1265009, 4055324, 1247620, 2486353, 1595974, 2619752, 3539968, 8079950, 7709315, 7151892, 8357436, 7072248, 4613401, 1250494, 2635921, 4832145, 5386378, 1869119, 1903435, 7329447, 6271868, 2348700, 7841118, 7998430, 1349076, 1852771, 6949987, 7047359, 1237275, 5062207, 6950192, 7929317, 1312455, 3306115, 6417775, 6262231, 6681150, 6736599, 5037034, 264944, 508951, 3097992, 7100756, 1917081, 5834105, 7005614, 1500165, 777191, 2235880, 3406031, 4520680, 3505694, 4558682, 44288, 7280319, 904516, 3958618, 7838005, 5548557, 6709241, 6533464, 5796124, 4656147, 594136, 4603424, 6980856, 3507263, 6239768, 4656075, 8371839, 1653064, 5130689, 6366809, 2432395, 2454455, 8215696, 1957272, 3369112, 185531, 7173032, 5102745, 6779997, 3699596, 2389356, 8169440, 759969, 7063561, 5196991, 162844, 1616392, 3014001, 810149, 1652634, 4686184, 6581310, 1757237, 811944, 531354, 189548, 4827145, 3159746, 6529015, 5341501, 3523897, 3866901, 269760, 2213111, 7404533, 1717735, 472078, 8360995, 954230, 3881043, 5971092, 8202977, 1315589, 1341330, 7953734, 1723600, 6577327, 1910376, 6712985, 7276084, 8119771, 4546524, 4010497, 3900724, 5823537, 1285669, 6795489, 7567685, 6940675, 5441381, 6144432, 7959518, 6094090, 183443, 7403526, 1612842, 4834730, 280005, 2071892, 5582638, 5361315, 4499357, 4751448, 3839961, 7826001, 3919660, 8332111, 7018208, 3937738, 1400424, 7534263, 1976782].getD i 0

theorem tblv_eq : ∀ i, i < 240 → tblv i = nttRecG i := by decide +kernel

theorem tblv_lt : ∀ i, i < 240 → tblv i < 2 ^ 256 := by decide +kernel

/-- Block `k`'s 30 stores on top of `M`. -/
def tblChunk (M : ByteArray) (k : Nat) : ByteArray :=
  storeWords M (TBL + 960 * k) (fun i => tblv (30 * k + i)) 30

/-- Memory after the first `k` blocks. -/
def tblMem (m : ByteArray) : Nat → ByteArray
  | 0 => m
  | k + 1 => tblChunk (tblMem m k) k

theorem tblMem_frame (m : ByteArray) : ∀ k, FrameExcept m (tblMem m k) [(TBL, TBL + 960 * k)]
  | 0 => FrameExcept.refl _ _
  | k + 1 => by
    show FrameExcept m (tblChunk (tblMem m k) k) _
    unfold tblChunk
    apply FrameExcept.mono ((tblMem_frame m k).trans
      (FrameExcept.storeWords (tblMem m k) (TBL + 960 * k) (fun i => tblv (30 * k + i)) 30))
    intro r hr
    refine ⟨(TBL, TBL + 960 * (k + 1)), by simp, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> constructor <;> simp only <;> omega

theorem word_tblMem (m : ByteArray) : ∀ k, k ≤ 8 → ∀ i, i < 30 * k →
    word (tblMem m k) (TBL + 32 * i) = tblv i
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, hk, i, hi => by
    simp only [tblMem, tblChunk]
    by_cases h : 30 * k ≤ i
    · have := word_storeWords (m := tblMem m k) (base := TBL + 960 * k)
        (v := fun i => tblv (30 * k + i)) (i := i - 30 * k) (tblv_lt _ (by omega)) 30 (by omega)
      rw [show TBL + 960 * k + 32 * (i - 30 * k) = TBL + 32 * i by omega,
        show 30 * k + (i - 30 * k) = i by omega] at this
      exact this
    · rw [FrameExcept.word (FrameExcept.storeWords _ _ _ 30) (by
        simp only [avoids_cons, avoids_nil, and_true]; omega)]
      exact word_tblMem m k (by omega) i (by omega)

end MlDsaOptGlam44.Proofs
