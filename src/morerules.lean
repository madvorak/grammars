import onerule


-- Definitions

def ruleset := finset production_rule

def transformed (rules : ruleset) (oldWord newWord : string) : Prop :=
∃ r ∈ rules.val, transforms r oldWord newWord

inductive derives (rules : ruleset) : string → string → Prop
| step_base (word : string) : derives word word
| step_indu (startWord intermediate endWord : string) :
    transformed rules startWord intermediate → derives intermediate endWord → 
      derives startWord endWord



-- Demonstrations

def abb : ruleset := finset.mk [a_bb] (by simp)

example : derives abb "vana" "vbbnbb" :=
begin
  apply derives.step_indu "vana" "vbbna" "vbbnbb",
  {
    use a_bb,
    use "v",
    use "na",
    finish,
  },
  apply derives.step_indu "vbbna" "vbbnbb" "vbbnbb",
  {
    use a_bb,
    use "vbbn",
    use "",
    finish,
  },
  apply derives.step_base,
end


def cb_cac := production_rule.mk "cb" "cac"

def tworules : ruleset := finset.mk [a_bb, cb_cac] sorry

example : derives tworules "ca" "cacbcac" :=
begin
  have omg : cb_cac ∈ tworules.val,
  {
    unfold tworules,
    simp,
  },

  fconstructor,
  use "cbb",
  {
    use a_bb,
    use "c",
    use "",
    finish,
  },
  fconstructor,
  use "cacb",
  {
    use cb_cac,
    split,
      exact omg,
    use "",
    use "b",
    finish,
  },
  fconstructor,
  use "cacac", 
  {
    use cb_cac,
    split,
      exact omg,
    use "ca",
    use "",
    finish,
  },
  fconstructor,
  use "cbbcac",
  {
    use a_bb,
    use "c",
    use "cac",
    finish,
  },
  fconstructor,
  use "cacbcac", 
  {
    use cb_cac,
    split,
      exact omg,
    use "",
    use "bcac",
    finish,
  },
  fconstructor,
end
