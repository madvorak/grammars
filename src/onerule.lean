import tactic
import data.list


-- Definitions

structure production_rule := (input output : string)

def transforms (rule : production_rule) (oldWord newWord : string) : Prop :=
∃ v w : string, v ++ rule.input ++ w = oldWord ∧ v ++ rule.output ++ w = newWord


-- Demonstrations

def a_bb := production_rule.mk "a" "bb"

example : transforms a_bb "lack" "lbbck" :=
begin
  unfold transforms,
  use "l",
  use "ck",
  split;
  refl,
end

example : transforms a_bb "ahoj" "bbhoj" :=
begin
  --unfold transforms,
  use "",
  use "hoj",
  exact dec_trivial,
end

example : transforms a_bb "vana" "vanbb" :=
begin
  use "van",
  use "",
  tauto,
end

example : transforms a_bb "vana" "vbbna" :=
begin
  use "v",
  use "na",
  finish,
end

example : ¬ (transforms a_bb "lack" "labck") :=
begin
  intro assum,
  unfold transforms at assum,
  --rw a_bb at assum,
  have lit_in : a_bb.input = "a", refl,
  have lit_out : a_bb.output = "bb", refl,
  rw lit_in at assum,
  rw lit_out at assum,
  cases assum with v assum_,
  cases assum_ with w assum__,
  cases assum__ with hyp_before hyp_after,
  have left_side : v = "l",
  {
    sorry
  },
  have right_side : w = "ck",
  {
    rw left_side at hyp_before,
    have foo: "l" ++ "a" = "la", refl,
    rw foo at hyp_before,
    have bar: "lack" = "la" ++ "ck", refl,
    rw bar at hyp_before,
    sorry,
    --exact list.append_inj_right hyp_before id,
  },
  rw left_side at hyp_after,
  rw right_side at hyp_after,
  have concaten : "l" ++ "bb" ++ "ck" = "lbbck", refl,
  rw concaten at hyp_after,
  finish,
end
