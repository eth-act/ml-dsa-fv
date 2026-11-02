import MlDsaOptGlam87.Main.S1.Tac
import MlDsaOptGlam44.Main.Tbl.Defs
import MlDsaOptGlam87.Layout
import MlDsaOptGlam87.Budget
set_option warningAsError true
set_option maxHeartbeats 0
/-! # Segment `140 … 2059`: the 240 records of the 4 + 4 NTT's table (straight line).

Glam 44's segment `99 … 2018` (`MlDsaOptGlam44/Main/Tbl/Blocks.lean`, shifted; the
same instructions, checked when this file was made): eight blocks of 30
`PUSH v; PUSH2 TBL + 32 i; MSTORE` records. The chunks (`tblChunk`, `tblMem`) and
the record values (`tblv = nttRecG`) are glam 44's. -/

namespace MlDsaOptGlam87.Proofs.S1

open MlDsaOpt87.Proofs

open EvmSemantics
open EvmSemantics.EVM
open MlDsaOptCommon
open MlDsa
open MlDsaOptGlam87.Proofs.Infra
open MlDsaOptGlam44.Proofs (tblv tblv_eq tblChunk tblMem tblMem_frame word_tblMem)

theorem tbl_b0 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 140 [flag b] M) (callState s 380 [flag b] (tblChunk M 0)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]

theorem tbl_b1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 380 [flag b] M) (callState s 620 [flag b] (tblChunk M 1)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]

theorem tbl_b2 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 620 [flag b] M) (callState s 860 [flag b] (tblChunk M 2)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299]

theorem tbl_b3 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 860 [flag b] M) (callState s 1100 [flag b] (tblChunk M 3)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389]

theorem tbl_b4 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1100 [flag b] M) (callState s 1339 [flag b] (tblChunk M 4)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]

theorem tbl_b5 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1339 [flag b] M) (callState s 1579 [flag b] (tblChunk M 5)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569]

theorem tbl_b6 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1579 [flag b] M) (callState s 1819 [flag b] (tblChunk M 6)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659]

theorem tbl_b7 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1819 [flag b] M) (callState s 2059 [flag b] (tblChunk M 7)) 270 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2897 ≤ s.activeWords.toNat := hs.sized
  simp only [tblChunk, storeWords_succ, storeWords_zero]
  glam87_rreach [660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749]

theorem seg_tbl_proof {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv1 cd m) (b : Bool) :
    ∃ m', Inv2 cd m' ∧
      Reach (callState s 140 [flag b] m) (callState s 2059 [flag b] m') Gas.pTbl := by
  have hfr : FrameExcept m (tblMem m 8) [(TBL, TBL + 7680)] := tblMem_frame m 8
  refine ⟨tblMem m 8,
    ⟨trivial, trivial, fun i hi => ?_, ZAt.frame hI.z hfr (by s1_avoids87),
      ZeroOn.frame (ZeroOn.mono hI.zLow (by unfold MISC; omega) (by unfold TBL ZH; omega)) hfr
        (by s1_avoids87),
      ZeroOn.frame (ZeroOn.mono hI.zLow (by unfold MISC CW; omega) (by unfold ABUF ZH; omega)) hfr
        (by s1_avoids87),
      ZeroOn.frame hI.zHigh hfr (by s1_avoids87)⟩, ?_⟩
  · rw [word_tblMem m 8 le_rfl i (by omega), tblv_eq i hi]
  · exact ((((((((tbl_b0 hs b m).trans (tbl_b1 hs b _)).trans (tbl_b2 hs b _)).trans (tbl_b3 hs b _)).trans (tbl_b4 hs b _)).trans (tbl_b5 hs b _)).trans (tbl_b6 hs b _)).trans (tbl_b7 hs b _)).mono (by unfold Gas.pTbl; omega)

end MlDsaOptGlam87.Proofs.S1
