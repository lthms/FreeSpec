Require Import FreeSpec.Libs.Vector.Vector.

Definition bit := bool.

Notation "'Ox'" := vnil.

Notation "x '_0_'" := (vcons false (vcons false (vcons false (vcons false x))))
                       (at level 20).
Notation "x '_1_'" := (vcons true (vcons false (vcons false (vcons false x))))
                       (at level 20).
Notation "x '_2_'" := (vcons false (vcons true (vcons false (vcons false x))))
                       (at level 20).
Notation "x '_3_'" := (vcons true (vcons true (vcons false (vcons false x))))
                       (at level 20).
Notation "x '_4_'" := (vcons false (vcons false (vcons true (vcons false x))))
                       (at level 20).
Notation "x '_5_'" := (vcons true (vcons false (vcons true (vcons false x))))
                       (at level 20).
Notation "x '_6_'" := (vcons false (vcons true (vcons true (vcons false x))))
                       (at level 20).
Notation "x '_7_'" := (vcons true (vcons true (vcons true (vcons false x))))
                       (at level 20).
Notation "x '_8_'" := (vcons false (vcons false (vcons false (vcons true x))))
                       (at level 20).
Notation "x '_9_'" := (vcons true (vcons false (vcons false (vcons true x))))
                      (at level 20).
Notation "x '_A_'" := (vcons false (vcons true (vcons false (vcons true x))))
                        (at level 20).
Notation "x '_B_'" := (vcons true (vcons true (vcons false (vcons true x))))
                        (at level 20).
Notation "x '_C_'" := (vcons false (vcons false (vcons true (vcons true x))))
                        (at level 20).
Notation "x '_D_'" := (vcons true (vcons false (vcons true (vcons true x))))
                        (at level 20).
Notation "x '_E_'" := (vcons false (vcons true (vcons true (vcons true x))))
                        (at level 20).
Notation "x '_F_'" := (vcons true (vcons true (vcons true (vcons true x))))
                      (at level 20).
Notation "x '_00_'" := (x _0_ _0_)
                        (at level 20).
Notation "x '_01_'" := (x _0_ _1_)
                        (at level 20).
Notation "x '_02_'" := (x _0_ _2_)
                        (at level 20).
Notation "x '_03_'" := (x _0_ _3_)
                        (at level 20).
Notation "x '_04_'" := (x _0_ _4_)
                        (at level 20).
Notation "x '_05_'" := (x _0_ _5_)
                        (at level 20).
Notation "x '_06_'" := (x _0_ _6_)
                        (at level 20).
Notation "x '_07_'" := (x _0_ _7_)
                        (at level 20).
Notation "x '_08_'" := (x _0_ _8_)
                        (at level 20).
Notation "x '_09_'" := (x _0_ _9_)
                        (at level 20).
Notation "x '_0A_'" := (x _0_ _A_)
                        (at level 20).
Notation "x '_0B_'" := (x _0_ _B_)
                        (at level 20).
Notation "x '_0C_'" := (x _0_ _C_)
                        (at level 20).
Notation "x '_0D_'" := (x _0_ _D_)
                        (at level 20).
Notation "x '_0E_'" := (x _0_ _E_)
                        (at level 20).
Notation "x '_0F_'" := (x _0_ _F_)
                        (at level 20).
Notation "x '_10_'" := (x _1_ _0_)
                        (at level 20).
Notation "x '_11_'" := (x _1_ _1_)
                        (at level 20).
Notation "x '_12_'" := (x _1_ _2_)
                        (at level 20).
Notation "x '_13_'" := (x _1_ _3_)
                        (at level 20).
Notation "x '_14_'" := (x _1_ _4_)
                        (at level 20).
Notation "x '_15_'" := (x _1_ _5_)
                        (at level 20).
Notation "x '_16_'" := (x _1_ _6_)
                        (at level 20).
Notation "x '_17_'" := (x _1_ _7_)
                        (at level 20).
Notation "x '_18_'" := (x _1_ _8_)
                        (at level 20).
Notation "x '_19_'" := (x _1_ _9_)
                        (at level 20).
Notation "x '_1A_'" := (x _1_ _A_)
                        (at level 20).
Notation "x '_1B_'" := (x _1_ _B_)
                        (at level 20).
Notation "x '_1C_'" := (x _1_ _C_)
                        (at level 20).
Notation "x '_1D_'" := (x _1_ _D_)
                        (at level 20).
Notation "x '_1E_'" := (x _1_ _E_)
                        (at level 20).
Notation "x '_1F_'" := (x _1_ _F_)
                        (at level 20).
Notation "x '_20_'" := (x _2_ _0_)
                        (at level 20).
Notation "x '_21_'" := (x _2_ _1_)
                        (at level 20).
Notation "x '_22_'" := (x _2_ _2_)
                        (at level 20).
Notation "x '_23_'" := (x _2_ _3_)
                        (at level 20).
Notation "x '_24_'" := (x _2_ _4_)
                        (at level 20).
Notation "x '_25_'" := (x _2_ _5_)
                        (at level 20).
Notation "x '_26_'" := (x _2_ _6_)
                        (at level 20).
Notation "x '_27_'" := (x _2_ _7_)
                        (at level 20).
Notation "x '_28_'" := (x _2_ _8_)
                        (at level 20).
Notation "x '_29_'" := (x _2_ _9_)
                        (at level 20).
Notation "x '_2A_'" := (x _2_ _A_)
                        (at level 20).
Notation "x '_2B_'" := (x _2_ _B_)
                        (at level 20).
Notation "x '_2C_'" := (x _2_ _C_)
                        (at level 20).
Notation "x '_2D_'" := (x _2_ _D_)
                        (at level 20).
Notation "x '_2E_'" := (x _2_ _E_)
                        (at level 20).
Notation "x '_2F_'" := (x _2_ _F_)
                        (at level 20).
Notation "x '_30_'" := (x _3_ _0_)
                        (at level 20).
Notation "x '_31_'" := (x _3_ _1_)
                        (at level 20).
Notation "x '_32_'" := (x _3_ _2_)
                        (at level 20).
Notation "x '_33_'" := (x _3_ _3_)
                        (at level 20).
Notation "x '_34_'" := (x _3_ _4_)
                        (at level 20).
Notation "x '_35_'" := (x _3_ _5_)
                        (at level 20).
Notation "x '_36_'" := (x _3_ _6_)
                        (at level 20).
Notation "x '_37_'" := (x _3_ _7_)
                        (at level 20).
Notation "x '_38_'" := (x _3_ _8_)
                        (at level 20).
Notation "x '_39_'" := (x _3_ _9_)
                        (at level 20).
Notation "x '_3A_'" := (x _3_ _A_)
                        (at level 20).
Notation "x '_3B_'" := (x _3_ _B_)
                        (at level 20).
Notation "x '_3C_'" := (x _3_ _C_)
                        (at level 20).
Notation "x '_3D_'" := (x _3_ _D_)
                        (at level 20).
Notation "x '_3E_'" := (x _3_ _E_)
                        (at level 20).
Notation "x '_3F_'" := (x _3_ _F_)
                        (at level 20).
Notation "x '_40_'" := (x _4_ _0_)
                        (at level 20).
Notation "x '_41_'" := (x _4_ _1_)
                        (at level 20).
Notation "x '_42_'" := (x _4_ _2_)
                        (at level 20).
Notation "x '_43_'" := (x _4_ _3_)
                        (at level 20).
Notation "x '_44_'" := (x _4_ _4_)
                        (at level 20).
Notation "x '_45_'" := (x _4_ _5_)
                        (at level 20).
Notation "x '_46_'" := (x _4_ _6_)
                        (at level 20).
Notation "x '_47_'" := (x _4_ _7_)
                        (at level 20).
Notation "x '_48_'" := (x _4_ _8_)
                        (at level 20).
Notation "x '_49_'" := (x _4_ _9_)
                        (at level 20).
Notation "x '_4A_'" := (x _4_ _A_)
                        (at level 20).
Notation "x '_4B_'" := (x _4_ _B_)
                        (at level 20).
Notation "x '_4C_'" := (x _4_ _C_)
                        (at level 20).
Notation "x '_4D_'" := (x _4_ _D_)
                        (at level 20).
Notation "x '_4E_'" := (x _4_ _E_)
                        (at level 20).
Notation "x '_4F_'" := (x _4_ _F_)
                        (at level 20).
Notation "x '_50_'" := (x _5_ _0_)
                        (at level 20).
Notation "x '_51_'" := (x _5_ _1_)
                        (at level 20).
Notation "x '_52_'" := (x _5_ _2_)
                        (at level 20).
Notation "x '_53_'" := (x _5_ _3_)
                        (at level 20).
Notation "x '_54_'" := (x _5_ _4_)
                        (at level 20).
Notation "x '_55_'" := (x _5_ _5_)
                        (at level 20).
Notation "x '_56_'" := (x _5_ _6_)
                        (at level 20).
Notation "x '_57_'" := (x _5_ _7_)
                        (at level 20).
Notation "x '_58_'" := (x _5_ _8_)
                        (at level 20).
Notation "x '_59_'" := (x _5_ _9_)
                        (at level 20).
Notation "x '_5A_'" := (x _5_ _A_)
                        (at level 20).
Notation "x '_5B_'" := (x _5_ _B_)
                        (at level 20).
Notation "x '_5C_'" := (x _5_ _C_)
                        (at level 20).
Notation "x '_5D_'" := (x _5_ _D_)
                        (at level 20).
Notation "x '_5E_'" := (x _5_ _E_)
                        (at level 20).
Notation "x '_5F_'" := (x _5_ _F_)
                        (at level 20).
Notation "x '_60_'" := (x _6_ _0_)
                        (at level 20).
Notation "x '_61_'" := (x _6_ _1_)
                        (at level 20).
Notation "x '_62_'" := (x _6_ _2_)
                        (at level 20).
Notation "x '_63_'" := (x _6_ _3_)
                        (at level 20).
Notation "x '_64_'" := (x _6_ _4_)
                        (at level 20).
Notation "x '_65_'" := (x _6_ _5_)
                        (at level 20).
Notation "x '_66_'" := (x _6_ _6_)
                        (at level 20).
Notation "x '_67_'" := (x _6_ _7_)
                        (at level 20).
Notation "x '_68_'" := (x _6_ _8_)
                        (at level 20).
Notation "x '_69_'" := (x _6_ _9_)
                        (at level 20).
Notation "x '_6A_'" := (x _6_ _A_)
                        (at level 20).
Notation "x '_6B_'" := (x _6_ _B_)
                        (at level 20).
Notation "x '_6C_'" := (x _6_ _C_)
                        (at level 20).
Notation "x '_6D_'" := (x _6_ _D_)
                        (at level 20).
Notation "x '_6E_'" := (x _6_ _E_)
                        (at level 20).
Notation "x '_6F_'" := (x _6_ _F_)
                        (at level 20).
Notation "x '_70_'" := (x _7_ _0_)
                        (at level 20).
Notation "x '_71_'" := (x _7_ _1_)
                        (at level 20).
Notation "x '_72_'" := (x _7_ _2_)
                        (at level 20).
Notation "x '_73_'" := (x _7_ _3_)
                        (at level 20).
Notation "x '_74_'" := (x _7_ _4_)
                        (at level 20).
Notation "x '_75_'" := (x _7_ _5_)
                        (at level 20).
Notation "x '_76_'" := (x _7_ _6_)
                        (at level 20).
Notation "x '_77_'" := (x _7_ _7_)
                        (at level 20).
Notation "x '_78_'" := (x _7_ _8_)
                        (at level 20).
Notation "x '_79_'" := (x _7_ _9_)
                        (at level 20).
Notation "x '_7A_'" := (x _7_ _A_)
                        (at level 20).
Notation "x '_7B_'" := (x _7_ _B_)
                        (at level 20).
Notation "x '_7C_'" := (x _7_ _C_)
                        (at level 20).
Notation "x '_7D_'" := (x _7_ _D_)
                        (at level 20).
Notation "x '_7E_'" := (x _7_ _E_)
                        (at level 20).
Notation "x '_7F_'" := (x _7_ _F_)
                        (at level 20).
Notation "x '_80_'" := (x _8_ _0_)
                        (at level 20).
Notation "x '_81_'" := (x _8_ _1_)
                        (at level 20).
Notation "x '_82_'" := (x _8_ _2_)
                        (at level 20).
Notation "x '_83_'" := (x _8_ _3_)
                        (at level 20).
Notation "x '_84_'" := (x _8_ _4_)
                        (at level 20).
Notation "x '_85_'" := (x _8_ _5_)
                        (at level 20).
Notation "x '_86_'" := (x _8_ _6_)
                        (at level 20).
Notation "x '_87_'" := (x _8_ _7_)
                        (at level 20).
Notation "x '_88_'" := (x _8_ _8_)
                        (at level 20).
Notation "x '_89_'" := (x _8_ _9_)
                        (at level 20).
Notation "x '_8A_'" := (x _8_ _A_)
                        (at level 20).
Notation "x '_8B_'" := (x _8_ _B_)
                        (at level 20).
Notation "x '_8C_'" := (x _8_ _C_)
                        (at level 20).
Notation "x '_8D_'" := (x _8_ _D_)
                        (at level 20).
Notation "x '_8E_'" := (x _8_ _E_)
                        (at level 20).
Notation "x '_8F_'" := (x _8_ _F_)
                        (at level 20).
Notation "x '_90_'" := (x _9_ _0_)
                        (at level 20).
Notation "x '_91_'" := (x _9_ _1_)
                        (at level 20).
Notation "x '_92_'" := (x _9_ _2_)
                        (at level 20).
Notation "x '_93_'" := (x _9_ _3_)
                        (at level 20).
Notation "x '_94_'" := (x _9_ _4_)
                        (at level 20).
Notation "x '_95_'" := (x _9_ _5_)
                        (at level 20).
Notation "x '_96_'" := (x _9_ _6_)
                        (at level 20).
Notation "x '_97_'" := (x _9_ _7_)
                        (at level 20).
Notation "x '_98_'" := (x _9_ _8_)
                        (at level 20).
Notation "x '_99_'" := (x _9_ _9_)
                        (at level 20).
Notation "x '_9A_'" := (x _9_ _A_)
                        (at level 20).
Notation "x '_9B_'" := (x _9_ _B_)
                        (at level 20).
Notation "x '_9C_'" := (x _9_ _C_)
                        (at level 20).
Notation "x '_9D_'" := (x _9_ _D_)
                        (at level 20).
Notation "x '_9E_'" := (x _9_ _E_)
                        (at level 20).
Notation "x '_9F_'" := (x _9_ _F_)
                        (at level 20).
Notation "x '_A0_'" := (x _A_ _0_)
                        (at level 20).
Notation "x '_A1_'" := (x _A_ _1_)
                        (at level 20).
Notation "x '_A2_'" := (x _A_ _2_)
                        (at level 20).
Notation "x '_A3_'" := (x _A_ _3_)
                        (at level 20).
Notation "x '_A4_'" := (x _A_ _4_)
                        (at level 20).
Notation "x '_A5_'" := (x _A_ _5_)
                        (at level 20).
Notation "x '_A6_'" := (x _A_ _6_)
                        (at level 20).
Notation "x '_A7_'" := (x _A_ _7_)
                        (at level 20).
Notation "x '_A8_'" := (x _A_ _8_)
                        (at level 20).
Notation "x '_A9_'" := (x _A_ _9_)
                        (at level 20).
Notation "x '_AA_'" := (x _A_ _A_)
                        (at level 20).
Notation "x '_AB_'" := (x _A_ _B_)
                        (at level 20).
Notation "x '_AC_'" := (x _A_ _C_)
                        (at level 20).
Notation "x '_AD_'" := (x _A_ _D_)
                        (at level 20).
Notation "x '_AE_'" := (x _A_ _E_)
                        (at level 20).
Notation "x '_AF_'" := (x _A_ _F_)
                        (at level 20).
Notation "x '_B0_'" := (x _B_ _0_)
                        (at level 20).
Notation "x '_B1_'" := (x _B_ _1_)
                        (at level 20).
Notation "x '_B2_'" := (x _B_ _2_)
                        (at level 20).
Notation "x '_B3_'" := (x _B_ _3_)
                        (at level 20).
Notation "x '_B4_'" := (x _B_ _4_)
                        (at level 20).
Notation "x '_B5_'" := (x _B_ _5_)
                        (at level 20).
Notation "x '_B6_'" := (x _B_ _6_)
                        (at level 20).
Notation "x '_B7_'" := (x _B_ _7_)
                        (at level 20).
Notation "x '_B8_'" := (x _B_ _8_)
                        (at level 20).
Notation "x '_B9_'" := (x _B_ _9_)
                        (at level 20).
Notation "x '_BA_'" := (x _B_ _A_)
                        (at level 20).
Notation "x '_BB_'" := (x _B_ _B_)
                        (at level 20).
Notation "x '_BC_'" := (x _B_ _C_)
                        (at level 20).
Notation "x '_BD_'" := (x _B_ _D_)
                        (at level 20).
Notation "x '_BE_'" := (x _B_ _E_)
                        (at level 20).
Notation "x '_BF_'" := (x _B_ _F_)
                        (at level 20).
Notation "x '_C0_'" := (x _C_ _0_)
                        (at level 20).
Notation "x '_C1_'" := (x _C_ _1_)
                        (at level 20).
Notation "x '_C2_'" := (x _C_ _2_)
                        (at level 20).
Notation "x '_C3_'" := (x _C_ _3_)
                        (at level 20).
Notation "x '_C4_'" := (x _C_ _4_)
                        (at level 20).
Notation "x '_C5_'" := (x _C_ _5_)
                        (at level 20).
Notation "x '_C6_'" := (x _C_ _6_)
                        (at level 20).
Notation "x '_C7_'" := (x _C_ _7_)
                        (at level 20).
Notation "x '_C8_'" := (x _C_ _8_)
                        (at level 20).
Notation "x '_C9_'" := (x _C_ _9_)
                        (at level 20).
Notation "x '_CA_'" := (x _C_ _A_)
                        (at level 20).
Notation "x '_CB_'" := (x _C_ _B_)
                        (at level 20).
Notation "x '_CC_'" := (x _C_ _C_)
                        (at level 20).
Notation "x '_CD_'" := (x _C_ _D_)
                        (at level 20).
Notation "x '_CE_'" := (x _C_ _E_)
                        (at level 20).
Notation "x '_CF_'" := (x _C_ _F_)
                        (at level 20).
Notation "x '_D0_'" := (x _D_ _0_)
                        (at level 20).
Notation "x '_D1_'" := (x _D_ _1_)
                        (at level 20).
Notation "x '_D2_'" := (x _D_ _2_)
                        (at level 20).
Notation "x '_D3_'" := (x _D_ _3_)
                        (at level 20).
Notation "x '_D4_'" := (x _D_ _4_)
                        (at level 20).
Notation "x '_D5_'" := (x _D_ _5_)
                        (at level 20).
Notation "x '_D6_'" := (x _D_ _6_)
                        (at level 20).
Notation "x '_D7_'" := (x _D_ _7_)
                        (at level 20).
Notation "x '_D8_'" := (x _D_ _8_)
                        (at level 20).
Notation "x '_D9_'" := (x _D_ _9_)
                        (at level 20).
Notation "x '_DA_'" := (x _D_ _A_)
                        (at level 20).
Notation "x '_DB_'" := (x _D_ _B_)
                        (at level 20).
Notation "x '_DC_'" := (x _D_ _C_)
                        (at level 20).
Notation "x '_DD_'" := (x _D_ _D_)
                        (at level 20).
Notation "x '_DE_'" := (x _D_ _E_)
                        (at level 20).
Notation "x '_DF_'" := (x _D_ _F_)
                        (at level 20).
Notation "x '_E0_'" := (x _E_ _0_)
                        (at level 20).
Notation "x '_E1_'" := (x _E_ _1_)
                        (at level 20).
Notation "x '_E2_'" := (x _E_ _2_)
                        (at level 20).
Notation "x '_E3_'" := (x _E_ _3_)
                        (at level 20).
Notation "x '_E4_'" := (x _E_ _4_)
                        (at level 20).
Notation "x '_E5_'" := (x _E_ _5_)
                        (at level 20).
Notation "x '_E6_'" := (x _E_ _6_)
                        (at level 20).
Notation "x '_E7_'" := (x _E_ _7_)
                        (at level 20).
Notation "x '_E8_'" := (x _E_ _8_)
                        (at level 20).
Notation "x '_E9_'" := (x _E_ _9_)
                        (at level 20).
Notation "x '_EA_'" := (x _E_ _A_)
                        (at level 20).
Notation "x '_EB_'" := (x _E_ _B_)
                        (at level 20).
Notation "x '_EC_'" := (x _E_ _C_)
                        (at level 20).
Notation "x '_ED_'" := (x _E_ _D_)
                        (at level 20).
Notation "x '_EE_'" := (x _E_ _E_)
                        (at level 20).
Notation "x '_EF_'" := (x _E_ _F_)
                        (at level 20).
Notation "x '_F0_'" := (x _F_ _0_)
                        (at level 20).
Notation "x '_F1_'" := (x _F_ _1_)
                        (at level 20).
Notation "x '_F2_'" := (x _F_ _2_)
                        (at level 20).
Notation "x '_F3_'" := (x _F_ _3_)
                        (at level 20).
Notation "x '_F4_'" := (x _F_ _4_)
                        (at level 20).
Notation "x '_F5_'" := (x _F_ _5_)
                        (at level 20).
Notation "x '_F6_'" := (x _F_ _6_)
                        (at level 20).
Notation "x '_F7_'" := (x _F_ _7_)
                        (at level 20).
Notation "x '_F8_'" := (x _F_ _8_)
                        (at level 20).
Notation "x '_F9_'" := (x _F_ _9_)
                        (at level 20).
Notation "x '_FA_'" := (x _F_ _A_)
                        (at level 20).
Notation "x '_FB_'" := (x _F_ _B_)
                        (at level 20).
Notation "x '_FC_'" := (x _F_ _C_)
                        (at level 20).
Notation "x '_FD_'" := (x _F_ _D_)
                        (at level 20).
Notation "x '_FE_'" := (x _F_ _E_)
                        (at level 20).
Notation "x '_FF_'" := (x _F_ _F_)
                        (at level 20).
