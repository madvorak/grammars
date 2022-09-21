import unrestricted.grammar

/-
Grammar for unary multiplication
{ a^m . b^n . c^(m*n) | m n ∈ ℕ }
example   2 * 3 = 6

          S
S → LR
          LR
L → aLX
          aaLXXR
R → BR
          aaLXXBBBR
XB → BXC
XC → CX
CB → BC
          aaLBBBCCCCCCXXR
XR → R
          aaLBBBCCCCCCR
LB → bL
          aabbbLCCCCCCR
L → K
          aabbbKCCCCCCR
KC → cK
          aabbbccccccKR
KR → ∅
          aabbbcccccc

0 * 0 = 0 goes S → LR → KR → ∅
3 * 0 = 0 goes S → LR → aLXR → aaLXXR → aaaLXXXR → aaaLXXR → aaaLXR → aaaLR → aaaKR → aaa
0 * 2 = 0 goes S → LR → LBR → LBBR → bLBR → bbLR → bbKR → bb
1 * 1 = 1 goes S → LR → aLXR → aLXBR → aLBXCR → aLBCXR → aLBCR → abLCR → abKCR → abcKR → abc
-/
