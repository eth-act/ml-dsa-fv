import MlDsaOpt44.Main.Base
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

theorem tbl_b0 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1085 [flag b] M) (callState s 1333 [flag b] (tblChunk M 0)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312]

theorem tbl_b1 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1333 [flag b] M) (callState s 1581 [flag b] (tblChunk M 1)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405]

theorem tbl_b2 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1581 [flag b] M) (callState s 1829 [flag b] (tblChunk M 2)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498]

theorem tbl_b3 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 1829 [flag b] M) (callState s 2077 [flag b] (tblChunk M 3)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]

theorem tbl_b4 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 2077 [flag b] M) (callState s 2325 [flag b] (tblChunk M 4)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684]

theorem tbl_b5 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 2325 [flag b] M) (callState s 2572 [flag b] (tblChunk M 5)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777]

theorem tbl_b6 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 2572 [flag b] M) (callState s 2820 [flag b] (tblChunk M 6)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870]

theorem tbl_b7 {s : State} (hs : Ctx s) (b : Bool) (M : ByteArray) :
    Reach (callState s 2820 [flag b] M) (callState s 3068 [flag b] (tblChunk M 7)) 279 := by
  have haw : s.activeWords.toNat ≤ 18446744073709551616 := hs.small
  have hfw : 2097 ≤ s.activeWords.toNat := hs.sized
  opt44_reach [871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963]

theorem seg_tbl_proof {s : State} (hs : Ctx s) {cd m : ByteArray} (hI : Inv1 cd m) (b : Bool) :
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
  · exact ((((((((tbl_b0 hs b m).trans (tbl_b1 hs b _)).trans (tbl_b2 hs b _)).trans (tbl_b3 hs b _)).trans (tbl_b4 hs b _)).trans (tbl_b5 hs b _)).trans (tbl_b6 hs b _)).trans (tbl_b7 hs b _)).mono (by unfold Gas.pTbl; omega)

end MlDsaOpt44.Proofs
