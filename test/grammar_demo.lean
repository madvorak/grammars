import unrestricted.grammar

/-
Grammar for unary multiplication
{ a^m . b^n . c^(m*n) | m n ∈ ℕ }
example   2 * 3 = 6

          S
S → LRE
          LRE
L → aLX
          aaLXXRE
R → BR
          aaLXXBBBRE
R → ∅
          aaLXXBBBE
XB → BXC
XC → CX
CB → BC
          aaLBBBCCCCCCXXXE
XE → E
          aaLBBBCCCCCCE
LB → bL
          aabbbLCCCCCCE
L → K
          aabbbKCCCCCCE
KC → cK
          aabbbccccccKE
KE → ∅
          aabbbcccccc

0 * 0 = 0 goes S → LRE → LE → KE → ∅
2 * 0 = 0 goes S → LRE → aLXRE → aaLXXRE → aaLXXE → aaLXE → aaLE → aaKE → aa
0 * 2 = 0 goes S → LRE → LBRE → LBBRE → LBBEE → bLBE → bbLE → bbKE → bb
-/
