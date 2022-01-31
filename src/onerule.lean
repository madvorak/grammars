import tactic
import data.list

def derives (ruleFrom ruleTo : string) (oldWord newWord : string) : Prop 
:= ∃ v w : string, v ++ ruleFrom ++ w = oldWord ∧ v ++ ruleTo ++ w = newWord

example : derives "a" "bb" "lack" "lbbck" :=
begin
  unfold derives,
  use "l",
  use "ck",
  tauto,
  --split;
  --refl,
end

example : derives "a" "bb" "ahoj" "bbhoj" :=
begin
  --unfold derives,
  use "",
  use "hoj",
  exact dec_trivial,
  --split;
  --refl,
end

example : derives "a" "bb" "vana" "vanbb" :=
begin
  --unfold derives,
  use "van",
  use "",
  finish,
  --split;
  --refl,
end

example : derives "a" "bb" "vana" "vbbna" :=
begin
  use "v",
  use "na",
  finish,
end

example : ¬ (derives "a" "bb" "lack" "labck") :=
begin
  intro assum,
  unfold derives at assum,
  cases assum with v assum_h,
  cases assum_h with w hyp,
  cases hyp with before after,
  have foo: v = "l",
  {
    sorry,
  },
  have bar: w = "ck",
  {
    rw foo at before,
    have easy: "lack" = "la" ++ "ck", finish,
    rw easy at before,
    have easie: "l" ++ "a" = "la", finish,
    rw easie at before,
    have befor: string.to_list "la" ++ string.to_list w =
                string.to_list "la" ++ string.to_list "ck",
    {
      sorry,
    },
    have wtf := list.append_left_cancel befor,
    have hope : list.as_string w.to_list = list.as_string "ck".to_list,
    {
      apply congr_arg,
      exact wtf,
    },
    rw string.as_string_inv_to_list at hope,
    rw string.as_string_inv_to_list at hope,
    exact hope,
  },
  have baz: "lbbck" = "labck",
  {
    rw foo at after,
    rw bar at after,
    finish,
  },
  finish,
end
