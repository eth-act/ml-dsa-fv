import MlDsaOpt44.Layout
set_option warningAsError true
/-! # The 248 NTT zeta records of segment `1085 … 3068`

`tblv` (the pushed record words), `tblChunk` (block `k`'s 31 stores) and
`tblMem` (memory after `k` blocks). Light module: the ML-DSA-65/87 table
segments reuse it without waiting for the ML-DSA-44 main-flow proofs. -/

namespace MlDsaOpt44.Proofs

open MlDsaOptCommon

/-- The record words as pushed by the code. -/
def tblv (i : Nat) : Nat := [1826347, 2725464, 1024112, 2706023, 95776, 3077325, 3530437, 2353451, 7300517, 3585928, 6718724, 4788269, 5842901, 3915439, 8021166, 7830929, 7260833, 4519302, 5336701, 3574422, 5512770, 6288512, 2619752, 6271868, 3539968, 8079950, 2348700, 7841118, 3119733, 6262231, 4520680, 6681150, 6736599, 3505694, 4558682, 5495562, 6980856, 5102745, 3507263, 6239768, 6779997, 3699596, 3111497, 1757237, 8360995, 811944, 531354, 954230, 3881043, 2680103, 4010497, 280005, 3900724, 5823537, 2071892, 5582638, 4450022, 2091667, 3407706, 6851714, 2316500, 3817976, 4702672, 5037939, 2244091, 5339162, 5933984, 4817955, 6927966, 266997, 2434439, 3475950, 7144689, 3513181, 2176455, 4860065, 4621053, 6795196, 7183191, 5187039, 7122806, 900702, 1859098, 1939314, 909542, 819034, 4296819, 495491, 6767243, 7380215, 8337157, 7857917, 5190273, 7725090, 5257975, 5223087, 2031748, 3207046, 4747489, 4823422, 7855319, 126922, 7611795, 4784579, 3412210, 342297, 286988, 7396998, 5942594, 4108315, 2147896, 3437287, 5038140, 2715295, 1735879, 203044, 5412772, 2842341, 2691481, 4686924, 5790267, 1265009, 7969390, 4055324, 1247620, 5903370, 2486353, 1595974, 7709315, 4613401, 1250494, 7151892, 2635921, 4832145, 8357436, 5386378, 1869119, 7072248, 1903435, 7329447, 7998430, 7047359, 1237275, 1349076, 5062207, 6950192, 1852771, 7929317, 1312455, 6949987, 3306115, 6417775, 5037034, 7100756, 1917081, 264944, 5834105, 7005614, 508951, 1500165, 777191, 3097992, 2235880, 3406031, 44288, 7838005, 5548557, 7280319, 6709241, 6533464, 904516, 5796124, 4656147, 3958618, 594136, 4603424, 4656075, 6366809, 2432395, 8371839, 2454455, 8215696, 1653064, 1957272, 3369112, 5130689, 185531, 7173032, 2389356, 5196991, 162844, 8169440, 1616392, 3014001, 759969, 810149, 1652634, 7063561, 4686184, 6581310, 189548, 5341501, 3523897, 4827145, 3866901, 269760, 3159746, 2213111, 7404533, 6529015, 1717735, 472078, 5971092, 7953734, 1723600, 8202977, 6577327, 1910376, 1315589, 6712985, 7276084, 1341330, 8119771, 4546524, 1285669, 5441381, 6144432, 6795489, 7959518, 6094090, 7567685, 183443, 7403526, 6940675, 1612842, 4834730, 5361315, 7826001, 3919660, 4499357, 8332111, 7018208, 4751448, 3937738, 1400424, 3839961, 7534263, 1976782].getD i 0

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

end MlDsaOpt44.Proofs
