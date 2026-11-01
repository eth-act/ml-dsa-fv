exec(open('MlDsaOpt44/Main/Wp11Gen/evmcost.py').read())
M8=int('ff00'*15+'ff',16); M16=int('ffff0000'*7+'ffff',16); M32=int('ffffffff00000000'*3+'ffffffff',16)
M64=2**64-1; REP=1+2**64+2**128+2**192
L=lambda a,b:', '.join(str(i) for i in range(idx[a],idx[b]))
spr=12392
# (start, end, kind, args)
out=[]
out.append(f'''import MlDsaOpt44.Main.Base
import MlDsaOpt44.Math.Bswap
import MlDsaOpt44.Math.SpongeBits
set_option warningAsError true
/-! # Segment `3078 … 3439`: `RHO1` (spread ρ and c̃ lanes, eight `spr` calls).

The byte-swapped calldata word `Y = bswapNet (word cd a)` (`a = 0`, then
`CTOFF`) stays on the stack; its lanes, top first, are spread by `spr` and
stored at `RHO1 + 32 i`: memory after `k` stores is `storeWords m RHO1 (rhoW cd) k`. -/

namespace MlDsaOpt44.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa44
open MlDsaOpt44.Proofs.Infra

/-- The mask / multiplier words below `Y`. -/
def rhoK (b : Bool) : List UInt256 :=
  [wd {REP}, wd {M64}, wd {M32}, wd {M16}, wd {M8}, flag b]

/-- The eight `RHO1` words. -/
def rhoW (cd : ByteArray) (i : Nat) : Nat :=
  if i < 4 then spread (le64 cd (8 * i)) else spread (le64 cd (CTOFF + 8 * (i - 4)))

theorem rhoW_lt (cd : ByteArray) (i : Nat) : rhoW cd i < 2 ^ 256 := by
  unfold rhoW; split <;> exact spread_lt _

theorem lane3_eq {{Y : Nat}} (h : Y < 2 ^ 256) : Y / 2 ^ 192 = lane Y 3 := by
  unfold lane; omega

theorem laneK_eq (Y k : Nat) : {M64} &&& Y / 2 ^ (64 * k) = lane Y k := by
  unfold lane
  rw [show ({M64} : Nat) = 2 ^ 64 - 1 by norm_num, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]

''')
hY='(hY : Y < 115792089237316195423570985008687907853269984665640564039457584007913129639936)'
pre='''  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2065 ≤ s.activeWords.toNat := hs.sized
'''
# network blocks
out.append(f'''
theorem rho_b0 {{s : State}} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 3078 [flag b] M)
      (callState s 3247 (wd (bswapNet (word s.executionEnv.calldata 0)) :: rhoK b) M) {cost(idx[3078],idx[3247])} := by
{pre}  opt44_reach [{L(3078,3247)}] with [rhoK, bswapNet, bsw8, bsw16, bsw32]
''')
# lane expressions
lanes={3:'Y / 2 ^ 192',2:f'{M64} &&& Y / 2 ^ (64 * 2)',1:f'{M64} &&& Y / 2 ^ (64 * 1)',0:f'{M64} &&& Y'}
# lane extraction blocks starting from JUMPDEST-after-network (b1, b6): no store
for name,a,e,ret in [('rho_b1',3247,3259,3259),('rho_b6',3362,3374,3374)]:
    out.append(f'''
theorem {name} {{s : State}} (hs : Ctx s) (b : Bool) (Y : Nat) {hY} (M : ByteArray) :
    Reach (callState s {a} (wd Y :: rhoK b) M)
      (callState s {spr} (wd ({lanes[3]}) :: wd {ret} :: wd Y :: rhoK b) M) {cost(idx[a],idx[e])} := by
{pre}  opt44_reach [{L(a,e)}] with [rhoK]
''')
# store + next lane blocks
for name,a,e,k,lanek,ret in [('rho_b2',3259,3278,0,2,3278),('rho_b3',3278,3297,1,1,3297),('rho_b4',3297,3313,2,0,3313),
                              ('rho_b7',3374,3393,4,2,3393),('rho_b8',3393,3412,5,1,3412),('rho_b9',3412,3428,6,0,3428)]:
    out.append(f'''
theorem {name} {{s : State}} (hs : Ctx s) (b : Bool) (Y : Nat) {hY if lanek else hY.replace('(hY','(_hY')} (m : ByteArray)
    (w : Nat → Nat) (hw : w {k} < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s {a} (wd (w {k}) :: wd Y :: rhoK b) (storeWords m RHO1 w {k}))
      (callState s {spr} (wd ({lanes[lanek]}) :: wd {ret} :: wd Y :: rhoK b)
        (storeWords m RHO1 w {k+1})) {cost(idx[a],idx[e])} := by
{pre}  opt44_reach [{L(a,e)}] with [rhoK]
  rfl
''')
out.append(f'''
theorem rho_b5 {{s : State}} (hs : Ctx s) (b : Bool) (Y : Nat) (m : ByteArray)
    (w : Nat → Nat) (hw : w 3 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3313 (wd (w 3) :: wd Y :: rhoK b) (storeWords m RHO1 w 3))
      (callState s 3362 (wd (bswapNet (word s.executionEnv.calldata 1312)) :: rhoK b)
        (storeWords m RHO1 w 4)) {cost(idx[3313],idx[3362])} := by
{pre}  opt44_reach [{L(3313,3362)}] with [rhoK, bswapNet, bsw8, bsw16, bsw32]
  rfl

theorem rho_b10 {{s : State}} (hs : Ctx s) (b : Bool) (Y : Nat) (m : ByteArray)
    (w : Nat → Nat) (hw : w 7 < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    Reach (callState s 3428 (wd (w 7) :: wd Y :: rhoK b) (storeWords m RHO1 w 7))
      (callState s 3439 [flag b] (storeWords m RHO1 w 8)) {cost(idx[3428],idx[3439])} := by
{pre}  opt44_reach [{L(3428,3439)}] with [rhoK]
  rfl
''')
M64s=str(M64)
out.append(open('MlDsaOpt44/Main/Wp11Gen/rho_tail.lean').read().replace('M64', M64s))
open('MlDsaOpt44/Main/Rho/Blocks.lean','w').write(''.join(out))
