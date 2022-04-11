import context_free.cfg

variable {T : Type}


/-- Context-free grammar for the empty language (i.e., `∈` always gives `false`). -/
def cfg_empty_lang : CF_grammar T :=
CF_grammar.mk (fin 1) 0 []

/-- Characterization of the empty language. -/
lemma language_of_cfg_empty_lang :
  CF_language (@cfg_empty_lang T) = 0 :=
begin
  unfold CF_language,
  ext1 w,
  split, swap,
  {
    intro h,
    exfalso,
    exact set.not_mem_empty w h,
  },
  intro hw,
  change CF_derives cfg_empty_lang [symbol.nonterminal cfg_empty_lang.initial] (list.map symbol.terminal w) at hw,
  exfalso,
  cases CF_tran_or_id_of_deri hw,
  {
    have hhead := congr_fun (congr_arg list.nth h) 0,
    cases w with head tail ih,
    {
      change some (symbol.nonterminal cfg_empty_lang.initial) = none at hhead,
      norm_cast at hhead,
    },
    {
      change some (symbol.nonterminal cfg_empty_lang.initial) = some (symbol.terminal head) at hhead,
      norm_cast at hhead,
    },
  },
  {
    rcases h with ⟨ v, ⟨ rul, rin, prefi, postfi, bef, aft ⟩, trash ⟩,
    clear trash,
    cases rin,
  },
end

/-- Context-free grammar for the singleton language that contains `[]` as its only word. -/
def cfg_empty_word : CF_grammar T :=
CF_grammar.mk (fin 1) 0 [(0, [])]

/-- Characterization of the singleton language. -/
lemma language_of_cfg_empty_word :
  CF_language (@cfg_empty_word T) = singleton [] :=
begin
  sorry,
end

/-- Context-free grammar for a language `{a}.star` where `a` is a given terminal symbol. -/
def cfg_symbol_star (a : T) : CF_grammar T :=
CF_grammar.mk (fin 1) 0 [(0, [symbol.terminal a, symbol.nonterminal 0]), (0, [])]

/-- Characterization of the `{a}.star` language. -/
lemma language_of_cfg_symbol_star (a : T) :
  CF_language (cfg_symbol_star a) = λ w, ∃ n : ℕ, w = list.repeat a n :=
begin
  apply set.eq_of_subset_of_subset,
  {

    sorry,
  },
  {
    intros w hw,
    cases hw with n hwn,
    rw hwn,
    change CF_generates_str (cfg_symbol_star a) (list.map symbol.terminal (list.repeat a n)),
    convert_to CF_generates_str (cfg_symbol_star a) _,
    unfold CF_generates_str,
    clear hwn w,
    have comes_to : CF_derives (cfg_symbol_star a)
                               [symbol.nonterminal (cfg_symbol_star a).initial]
                               (list.repeat (symbol.terminal a) n ++ [symbol.nonterminal (0 : fin 1)]),
    {
      induction n with n ih,
      {
        sorry,
      },
      
      sorry,
    },
    apply CF_deri_of_deri_tran comes_to,
    use ((0 : fin 1), []),
    split,
      sorry,
    use [list.repeat (symbol.terminal a) n, []],
    split;
    simp,
  }
end
