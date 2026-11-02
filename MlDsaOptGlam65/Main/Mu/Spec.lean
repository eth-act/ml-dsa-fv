import MlDsaOpt44.Main.Mu.Spec
import MlDsaOptGlam65.Main.Base
import MlDsaOptGlam65.Layout
import MlDsaOptGlam65.Budget
/- Ported from `MlDsaOpt65/Main/Mu/Spec.lean` by `scripts/proofgen_port.py --glam 65`; hand adjustments are marked `-- glam:`. -/
set_option maxHeartbeats 0  -- glam: re-elaboration headroom
set_option warningAsError true
/-!
# The SHAKE256 input of μ and its lanes

`muMsgW cd = tr ‖ 0 ‖ 0 ‖ M`; its bytes past `tr` are calldata bytes
(`le64_muMsgW_hi`), except that the two zero bytes are the masked low bytes of
the calldata lane at `5259` (`le64_muMsgW_64`). As `MlDsaOpt44/Main/Mu/Spec.lean` with `HDR = 5261`.
-/

namespace MlDsaOptGlam65.Proofs.S6Mu

open MlDsaOpt65.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs hiding ACC BASES BK CB CRep CTOFF Ctx Ctx.ctx0 Ctx0 Ctx0.callState FIN H0 HDR HP IDX KZ MU RHO1 RetOK Rho1At SP SibFresh TOP TRL TTable Z0 aD aOf azRow baseOf cD cOf cStream codeOf ctOf finBytes ginitWord hintD hintOf memWords mlenOf msgOf muOf nNeg negCount okA okC okH okZ optAccepts pkOf rawZ rhoOf sPrime sigOf spOff t1Of t1v tEntry trOf w1Of wRow zHat zHi zLane zLo zPolys

def muMsgW (cd : ByteArray) : ByteArray := trOf cd ++ (ByteArray.mk #[0, 0] ++ msgOf cd)

def muPad (cd : ByteArray) : ByteArray := Fips202.pad 136 0x1F (muMsgW cd)

theorem trOf_sizeW (cd : ByteArray) : (trOf cd).size = 64 := shake_size _ (by norm_num)

theorem muMsgW_size (cd : ByteArray) (hcd : HDR ≤ cd.size) :
    (muMsgW cd).size = 66 + (cd.size - 5261) := by
  unfold muMsgW msgOf
  rw [ByteArray.size_append, ByteArray.size_append, trOf_sizeW, ByteArray.size_extract]
  change 64 + (2 + _) = _
  unfold HDR at hcd ⊢
  omega

theorem byteAt_muMsgW (cd : ByteArray) (k : Nat) :
    byteAt (muMsgW cd) k =
      if k < 64 then byteAt (trOf cd) k else if k < 66 then 0 else byteAt cd (5195 + k) := by
  unfold muMsgW
  rw [byteAt_append, trOf_sizeW]
  split
  · rfl
  · rw [byteAt_append, show (ByteArray.mk #[(0 : UInt8), 0]).size = 2 from rfl]
    split
    · rw [if_pos (by omega)]; exact byteAt_pair0 _
    · rw [if_neg (by omega)]
      unfold msgOf HDR
      rw [byteAt_extract _ _ _ _ le_rfl]
      split
      · congr 1; omega
      · unfold byteAt; rw [dif_neg (by omega)]

theorem le64_muMsgW_lo (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (muMsgW cd) (8 * x) = le64 (trOf cd) (8 * x) :=
  le64_congr fun k hk => by rw [byteAt_muMsgW cd, if_pos (by omega)]

theorem le64_muMsgW_hi (cd : ByteArray) {a : Nat} (ha : 66 ≤ a) :
    le64 (muMsgW cd) a = le64 cd (5195 + a) :=
  le64_congr fun k hk => by
    rw [byteAt_muMsgW cd, if_neg (by omega), if_neg (by omega), Nat.add_assoc]

theorem le64_muMsgW_64 (cd : ByteArray) :
    le64 (muMsgW cd) 64 = 18446744073709486080 &&& le64 cd 5259 := by
  apply eq_of_byteN64 (le64_lt _ _) (mask48_lt _)
  intro i hi
  rw [byteN_le64 _ _ hi, byteN_and, byteN_le64 _ _ hi, byteAt_muMsgW cd, if_neg (by omega)]
  have hb := byteAt_lt cd (5259 + i)
  have hm : byteN 18446744073709486080 i = if i < 2 then 0 else 255 := by
    unfold byteN; interval_cases i <;> norm_num
  rw [hm]
  split
  · rw [if_pos (by omega), Nat.zero_and]
  · rw [if_neg (by omega), show 5195 + (64 + i) = 5259 + i by omega]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hb]

/-- `μ`'s lanes are the first lanes of the absorbed state. -/
theorem le64_muOf_absorb (cd : ByteArray) {x : Nat} (hx : x < 8) :
    le64 (muOf cd) (8 * x) = laneOf (Fips202.absorb 136 (muPad cd)) x := by
  have := le64_shake256 (muMsgW cd) (n := 64) (j := 0) (x := x) (by omega) (by omega)
  simpa [muOf, muMsgW, muPad, MlDsa.Fips204.H, MlDsa44.Fips204.H, Fips202.shake256] using this

end MlDsaOptGlam65.Proofs.S6Mu
