import context_free.cfg
import tactic


variables {T : Type}

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
    rcases h with ⟨v, ⟨rul, rin, prefi, postfi, bef, aft⟩, trash⟩,
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
  unfold CF_language,
  ext1 w,
  split, swap,
  {
    intro h,
    rw set.mem_singleton_iff at h,
    change CF_derives cfg_empty_word [symbol.nonterminal cfg_empty_lang.initial] (list.map symbol.terminal w),
    apply @CF_deri_of_tran,
    use ((0 : fin 1), []),
    use [[], []],
    rw h,
    split;
    refl,
    exact T,
  },
  intro hw,
  change
    CF_derives
      (@cfg_empty_word T)
      [symbol.nonterminal (@cfg_empty_lang T).initial]
      (list.map symbol.terminal w)
    at hw,
  cases
    @CF_tran_or_id_of_deri T
      (@cfg_empty_word T)
      [symbol.nonterminal cfg_empty_lang.initial]
      (list.map symbol.terminal w)
      hw,
  {
    exfalso,
    have zeroth := congr_fun (congr_arg list.nth h) 0,
    rw list.nth at zeroth,
    by_cases w = list.nil,
    {
      have is_none : (list.map symbol.terminal w).nth 0 = none,
      {
        rw h,
        rw list.nth_map,
        refl,
      },
      rw is_none at zeroth,
      exact option.no_confusion zeroth,
    },
    {
      have is_terminal : ∃ t, (list.map symbol.terminal w).nth 0 = some (symbol.terminal t),
      {
        apply exists.intro (w.nth_le 0 (list.length_pos_of_ne_nil h)),
        rw list.nth_map,
        norm_num,
        exact list.nth_le_nth (list.length_pos_of_ne_nil h),
      },
      cases is_terminal with irr is_termin,
      rw is_termin at zeroth,
      norm_cast at zeroth,
    },
  },
  rcases h with ⟨v, step_init, step_none⟩,
  have v_is_empty_word : v = list.nil,
  {
    rcases step_init with ⟨rul, rin, pre, pos, bef, aft⟩,
    have rule : rul = ((0 : fin 1), []),
    {
      rw ←list.mem_singleton,
      exact rin,
    },
    have empty_surrounding : pre = [] ∧ pos = [],
    {
      rw rule at bef,
      have bef_lenghts := congr_arg list.length bef,
      rw list.length_append_append at bef_lenghts,
      rw list.length_singleton at bef_lenghts,
      rw list.length_singleton at bef_lenghts,
      split,
      {
        have pre_zero : pre.length = 0,
        {
          clear_except bef_lenghts,
          linarith,
        },
        rw list.length_eq_zero at pre_zero,
        exact pre_zero,
      },
      {
        have pos_zero : pos.length = 0,
        {
          clear_except bef_lenghts,
          linarith,
        },
        rw list.length_eq_zero at pos_zero,
        exact pos_zero,
      },
    },
    rw empty_surrounding.1 at aft,
    rw empty_surrounding.2 at aft,
    rw rule at aft,
    exact aft,
  },
  rw v_is_empty_word at step_none,
  cases
    @CF_tran_or_id_of_deri T
      (@cfg_empty_word T)
      list.nil
      (list.map symbol.terminal w)
      step_none,
  {
    by_contradiction contra,
    have w_not_nil : w.length > 0,
    {
      apply list.length_pos_of_ne_nil,
      convert contra,
    },
    have impossible_lengths := congr_arg list.length h,
    rw list.length at impossible_lengths,
    rw list.length_map at impossible_lengths,
    rw ←impossible_lengths at w_not_nil,
    exact nat.lt_irrefl 0 w_not_nil,
  },
  {
    exfalso,
    rcases h with ⟨-, ⟨trash_r, -, trash_1, trash_2, impossible, -⟩, -⟩,
    have impossible_len := congr_arg list.length impossible,
    clear_except impossible_len,
    rw list.length_append_append at impossible_len,
    rw list.length_singleton at impossible_len,
    rw list.length at impossible_len,
    linarith,
  },
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
        apply contr,
        apply list.ext_le same_len,
        push_neg at isnt,
        intros n n_small_left n_small_right,
        specialize isnt n n_small_left,
        push_neg at isnt,
        specialize isnt n_small_right,
        push_neg at isnt,
        exact isnt,
      },
      rcases different with ⟨n, hl, hr, nq⟩,

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
          clear_except,
          rw list.mem_singleton,
          apply symbol.no_confusion,
        },
        rcases orig with ⟨rul, rin, p, q, bef, aft⟩,
        rw aft,
        rw bef at ih,
        repeat {
          rw list.mem_append at *,
        },
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
          dsimp only,
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
      rw ←list.cons_append,
      trim,
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
