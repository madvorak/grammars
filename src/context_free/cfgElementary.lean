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
    intro w,
    /-
      We prove this inclusion as follows:
      (1) `w ∈ CF_language (cfg_symbol_star a)` →
      (2) `w` contains only `a`s →
      (3) `∃ (n : ℕ), w = list.repeat a n)` □
    -/

    have implication2 : (∀ t : T, t ≠ a → t ∉ w) → (∃ (n : ℕ), w = list.repeat a n),
    {
      contrapose,
      intros contr ass,
      push_neg at contr,
      specialize contr w.length,

      have different :
        ∃ n : ℕ, ∃ hl : n < w.length, ∃ hr : n < (list.repeat a w.length).length,
          w.nth_le n hl ≠ (list.repeat a w.length).nth_le n hr,
      {
        by_contradiction isnt,
        have same_len : w.length = (list.repeat a w.length).length,
        {
          rw list.length_repeat,
        },
        apply contr ∘ list.ext_le same_len,
        push_neg at isnt,
        intros n n_small_left n_small_right,
        specialize isnt n n_small_left,
        push_neg at isnt,
        specialize isnt n_small_right,
        push_neg at isnt,
        exact isnt,
      },
      rcases different with ⟨ n, hl, hr, nq ⟩,

      rw list.nth_le_repeat a hr at nq,
      specialize ass (w.nth_le n hl) nq,
      exact ass (list.nth_le_mem w n hl),
    },

    have implication1 : w ∈ CF_language (cfg_symbol_star a) → (∀ t : T, t ≠ a → t ∉ w),
    {
      clear implication2,
      intros ass t nq,
      change CF_generates_str (cfg_symbol_star a) (list.map symbol.terminal w) at ass,
      unfold CF_generates_str at ass,

      have indu :
        ∀ v : list (symbol T (cfg_symbol_star a).nt),
          CF_derives (cfg_symbol_star a) [symbol.nonterminal (cfg_symbol_star a).initial] v →
            symbol.terminal t ∉ v,
      {
        intros v hyp,
        induction hyp with x y trash orig ih,
        {
          finish,
        },
        rcases orig with ⟨ rul, rin, p, q, bef, aft ⟩,
        rw aft,
        rw bef at ih,
        repeat { rw list.mem_append at * },
        push_neg,
        push_neg at ih,
        split, swap,
        {
          exact ih.right,
        },
        split,
        {
          exact ih.left.left,
        },
        cases rin,
        {
          rw rin,
          dsimp,
          intro imposs,
          cases imposs,
          {
            apply nq,
            exact symbol.terminal.inj imposs,
          },
          cases imposs,
          {
            norm_cast at imposs,
          },
          exact list.not_mem_nil (@symbol.terminal T (cfg_symbol_star a).nt t) imposs,
        },
        {
          change rul ∈ [((0 : fin 1), ([] : list (symbol T (cfg_symbol_star a).nt)))] at rin,
          rw list.mem_singleton at rin,
          rw rin,
          exact list.not_mem_nil (symbol.terminal t),
        }
      },
      specialize indu (list.map symbol.terminal w) ass,

      by_contradiction contra,
      exact indu (list.mem_map_of_mem symbol.terminal contra),
    },

    exact implication2 ∘ implication1,
  },
  {
    intros w hw,
    cases hw with n hwn,
    rw hwn,
    convert_to CF_generates_str (cfg_symbol_star a) (list.map symbol.terminal (list.repeat a n)),
    unfold CF_generates_str,
    clear hwn w,
    have comes_to :
      CF_derives
        (cfg_symbol_star a)
        [symbol.nonterminal (cfg_symbol_star a).initial]
        (list.repeat (symbol.terminal a) n ++ [symbol.nonterminal (0 : fin 1)]),
    {
      induction n with n ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran ih,
      use ((0 : fin 1), [symbol.terminal a, symbol.nonterminal (0 : fin 1)]),
      split,
      {
        apply list.mem_cons_self,
      },
      use [list.repeat (symbol.terminal a) n, []],
      split,
      {
        rw list.append_nil,
      },
      rw list.append_nil,
      change
        symbol.terminal a :: (list.repeat (symbol.terminal a) n ++ [symbol.nonterminal (0 : fin 1)]) =
        list.repeat (symbol.terminal a) n ++ ([symbol.terminal a] ++ [symbol.nonterminal 0]),
      rw ← list.append_assoc,
      rw ← list.cons_append,
      apply congr_arg2, swap,
      {
        refl,
      },
      have count_succ_left :
        @symbol.terminal T (fin 1) a :: list.repeat (symbol.terminal a) n =
        list.repeat (symbol.terminal a) (n + 1),
      {
        symmetry,
        apply list.repeat_succ,
      },
      have count_succ_right :
        list.repeat (symbol.terminal a) n ++ [symbol.terminal a] =
        list.repeat (symbol.terminal a) (n + 1),
      {
        change
          list.repeat (symbol.terminal a) n ++ list.repeat (symbol.terminal a) 1 =
          list.repeat (symbol.terminal a) (n + 1),
        symmetry,
        apply list.repeat_add,
      },
      rw count_succ_left,
      rw count_succ_right,
    },
    apply CF_deri_of_deri_tran comes_to,
    use ((0 : fin 1), []),
    split,
    {
      apply list.mem_cons_of_mem,
      apply list.mem_cons_self,
    },
    use [list.repeat (symbol.terminal a) n, []],
    split;
    simp,
  }
end
