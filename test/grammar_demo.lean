import unrestricted.grammar


inductive abeceda
| _a : abeceda
| _b : abeceda
| _c : abeceda

inductive vnitrni
| _S : vnitrni
| _L : vnitrni
| _R : vnitrni
| _X : vnitrni
| _B : vnitrni
| _C : vnitrni
| _K : vnitrni

private def a_ := abeceda._a
private def b_ := abeceda._b
private def c_ := abeceda._c

private def S_ := vnitrni._S
private def L_ := vnitrni._L
private def R_ := vnitrni._R
private def X_ := vnitrni._X
private def B_ := vnitrni._B
private def C_ := vnitrni._C
private def K_ := vnitrni._K

private def znak : Type := symbol abeceda vnitrni
private def pravidlo : Type := grule abeceda vnitrni

private def a : znak := symbol.terminal a_
private def b : znak := symbol.terminal b_
private def c : znak := symbol.terminal c_

private def S : znak := symbol.nonterminal vnitrni._S
private def L : znak := symbol.nonterminal vnitrni._L
private def R : znak := symbol.nonterminal vnitrni._R
private def X : znak := symbol.nonterminal vnitrni._X
private def B : znak := symbol.nonterminal vnitrni._B
private def C : znak := symbol.nonterminal vnitrni._C
private def K : znak := symbol.nonterminal vnitrni._K

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

private def S_LR   : pravidlo := grule.mk  [] S_ [] [L, R]
private def L_aLX  : pravidlo := grule.mk  [] L_ [] [a, L, X]
private def R_BR   : pravidlo := grule.mk  [] R_ [] [B, R]
private def XB_BXC : pravidlo := grule.mk [X] B_ [] [B, X, C]
private def XC_CX  : pravidlo := grule.mk [X] C_ [] [C, X]
private def CB_BC  : pravidlo := grule.mk [C] B_ [] [B, C]
private def XR_X   : pravidlo := grule.mk [X] R_ [] [X]
private def LB_bL  : pravidlo := grule.mk [L] B_ [] [b, L]
private def L_K    : pravidlo := grule.mk  [] L_ [] [K]
private def KC_cK  : pravidlo := grule.mk [K] C_ [] [c, K]
private def KR_end : pravidlo := grule.mk [K] R_ [] []

private def gr_mul : grammar abeceda :=
grammar.mk vnitrni S_ [S_LR, L_aLX, R_BR, XB_BXC, XC_CX, CB_BC, XR_X, LB_bL, L_K, KC_cK, KR_end]


example : grammar_generates gr_mul [] :=
begin
  unfold grammar_generates,

  apply grammar_deri_of_tran_deri,
  {
    use S_LR,
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  rw [list.nil_append, list.append_nil],

  apply grammar_deri_of_tran_deri,
  {
    use L_K,
    split,
    {
      repeat {
        try {
          apply list.mem_cons_self,
        },
        try {
          apply list.mem_cons_of_mem,
        },
      },
    },
    use [[], [R]],
    split;
    refl,
  },
  rw list.nil_append,

  apply grammar_deri_of_tran,
  {
    use KR_end,
    split,
    {
      repeat {
        try {
          apply list.mem_cons_self,
        },
        try {
          apply list.mem_cons_of_mem,
        },
      },
    },
    use [[], []],
    split;
    refl,
  },
end
