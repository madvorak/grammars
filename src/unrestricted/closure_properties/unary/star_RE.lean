import unrestricted.grammarLiftSink


variable {T : Type}

private def wrap_symbol {N : Type} : symbol T N → symbol T (option N)
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (some n)

private def wrap_grule {N : Type} (r : grule T N) : grule T (option N) :=
grule.mk
  (
    list.map wrap_symbol r.input_string.first,
    some r.input_string.secon,
    list.map wrap_symbol r.input_string.third
  )
  (list.map wrap_symbol r.output_string)

-- this cannot work; it generates a superset of L*
-- TODO redo completely
private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (option g.nt) none (
    (grule.mk ([], none, []) ([])) ::
    (grule.mk ([], none, []) ([symbol.nonterminal (some g.initial), symbol.nonterminal none])) ::
    (list.map wrap_grule g.rules)
  )


private lemma in_star_grammar_of_in_language_star {g₀ : grammar T} {w : list T}
    (h : w ∈ (grammar_language g₀).star) :
  grammar_generates (star_grammar g₀) w :=
begin
  rcases h with ⟨ parts, joined, each_part_in_lang ⟩,
  unfold grammar_generates,
  rw joined,
  clear_except each_part_in_lang,
  induction parts with head tail ih,
  {
    apply grammar_deri_of_tran,
    use (grule.mk ([], none, []) ([])),
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  specialize ih (by finish),
  have epoch_init :
    grammar_derives
      (star_grammar g₀)
      [symbol.nonterminal (star_grammar g₀).initial]
      ((list.map (@symbol.terminal T (option g₀.nt)) head) ++ [symbol.nonterminal none]),
  {
    clear ih,
    apply grammar_deri_of_tran_deri,
    {
      use grule.mk ([], none, []) ([symbol.nonterminal (some g₀.initial), symbol.nonterminal none]),
      split,
      {
        apply list.mem_cons_of_mem,
        apply list.mem_cons_self,
      },
      use [[], []],
      split;
      refl,
    },
    rw list.nil_append,
    rw list.append_nil,
    change
      grammar_derives
        (star_grammar g₀)
        ([symbol.nonterminal (some g₀.initial)] ++ [symbol.nonterminal none])
        (list.map symbol.terminal head ++ [symbol.nonterminal none]),
    apply grammar_derives_with_postfix,
    have head_in_lang := each_part_in_lang head (list.mem_cons_self head _),
    clear each_part_in_lang,
    unfold grammar_language at head_in_lang,
    rw set.mem_set_of_eq at head_in_lang,
    unfold grammar_generates at head_in_lang,
    have induc :
      ∀ v : list (symbol T g₀.nt),
        grammar_derives g₀ [symbol.nonterminal g₀.initial] v →
          grammar_derives (star_grammar g₀) [symbol.nonterminal (option.some g₀.initial)] (list.map wrap_symbol v),
    {
      intros w deri₀,
      induction deri₀ with u v trash orig ih,
      {
        apply grammar_deri_self,
      },
      apply grammar_deri_of_deri_tran ih,
      rcases orig with ⟨ r, rin, x, y, bef, aft ⟩,
      use wrap_grule r,
      split,
      {
        apply list.mem_cons_of_mem,
        apply list.mem_cons_of_mem,
        rw list.mem_map,
        use r,
        exact ⟨ rin, rfl ⟩,
      },
      use list.map wrap_symbol x,
      use list.map wrap_symbol y,

      have wrap_bef := congr_arg (list.map wrap_symbol) bef,
      rw list.map_append_append at wrap_bef,
      rw list.map_append_append at wrap_bef,
      rw list.map_singleton at wrap_bef,
      have wrap_aft := congr_arg (list.map wrap_symbol) aft,
      rw list.map_append_append at wrap_aft,
      clear_except wrap_bef wrap_aft,
      split,
      {
        convert wrap_bef,
      },
      {
        convert wrap_aft,
      },
    },
    specialize induc (list.map symbol.terminal head) head_in_lang,
    rw list.map_map at induc,
    convert induc,
  },
  apply grammar_deri_of_deri_deri epoch_init,
  clear epoch_init,
  rw list.map_join,
  rw list.map_cons,
  apply grammar_derives_with_prefix (list.map symbol.terminal head),
  rw ← list.map_join,
  exact ih,
end


section difficult_direction

private def oT_of_sTN {g : grammar T} : symbol T g.nt → option T
| (symbol.terminal t) := some t
| (symbol.nonterminal _) := none

private lemma big_induction {g₀ : grammar T} :
  ∀ v : list (symbol T (star_grammar g₀).nt),
    grammar_derives (star_grammar g₀) [symbol.nonterminal (star_grammar g₀).initial] v →
      ∃ (S : list (list (symbol T g₀.nt))), and (or
          (v = (list.map (list.map wrap_symbol) S).join)
          (v = (list.map (list.map wrap_symbol) S).join ++ [symbol.nonterminal none]))
        (∀ (u : list (symbol T g₀.nt)), u ∈ S → grammar_derives g₀ [symbol.nonterminal g₀.initial] u) :=
begin
  intros v hgdv,
  induction hgdv with x y trash orig ih,
  {
    use list.nil,
    split,
    {
      right,
      refl,
    },
    {
      intros u u_in_nil,
      exfalso,
      exact list.not_mem_nil u u_in_nil,
    },
  },
  rcases ih with ⟨S, compoS, validity⟩,
  rcases orig with ⟨r, rin, u, w, bef, aft⟩,
  --cases list.eq_or_mem_of_mem_cons rin,
  cases rin,
  {
    -- could match only at the last position
    rw rin at *,
    clear rin,
    dsimp at *,
    cases compoS,
    {
      exfalso,
      rw bef at compoS,
      clear_except compoS,
      rw ← list.map_join at compoS,
      have none_in := congr_arg (λ l, symbol.nonterminal none ∈ l) compoS,
      simp at none_in,
      rcases none_in with ⟨a, -, b, -, imposs⟩,
      clear_except imposs,
      cases b,
      {
        tauto,
      },
      {
        change symbol.nonterminal (some b) = symbol.nonterminal none at imposs,
        rw symbol.nonterminal.inj_eq at imposs,
        tauto,
      },
    },
    have w_has_nothing : w = [],
    {
      rw bef at compoS,
      clear_except compoS,
      rw list.append_nil at compoS,
      rw list.append_nil at compoS,
      rw ← list.length_eq_zero,
      by_contradiction contra,
      change w.length ≠ 0 at contra,
      rw ← pos_iff_ne_zero at contra,
      have ul_lt : u.length < (list.map wrap_symbol S.join).length,
      {
        have lens := congr_arg list.length compoS,
        clear compoS,
        repeat { rw list.length_append at lens },
        repeat { rw list.length_singleton at lens },
        rw list.map_join,
        linarith,
      },
      have ulth := congr_fun (congr_arg list.nth compoS) u.length,
      clear compoS,

      have trivi_ul : u.length < (u ++ [symbol.nonterminal none]).length,
      {
        rw list.length_append,
        rw list.length_singleton,
        apply lt_add_one,
      },
      rw list.nth_append trivi_ul at ulth,
      rw list.nth_concat_length at ulth,

      rw ← list.map_join at ulth,
      rw list.nth_append ul_lt at ulth,
      clear_except ulth,
      rw list.nth_map at ulth,
      cases S.join.nth u.length,
      {
        tauto,
      },
      {
        dsimp at ulth,
        rw option.some.inj_eq at ulth,
        cases val,
        {
          unfold wrap_symbol at ulth,
          tauto,
        },
        {
          unfold wrap_symbol at ulth,
          rw symbol.nonterminal.inj_eq at ulth,
          tauto,
        },
      },
    },
    have u_has_everything : u = (list.map (list.map wrap_symbol) S).join,
    {
      rw bef at compoS,
      rw w_has_nothing at compoS,
      repeat { rw list.append_nil at compoS },
      rw list.append_left_inj at compoS,
      exact compoS,
    },
    rw [ u_has_everything, w_has_nothing ] at *,
    clear u_has_everything w_has_nothing,
    simp only [list.append_nil] at *,
    use S,
    split,
    {
      -- one-way change from ending with `none` to ending with `some n` or with a terminal
      left,
      exact aft,
    },
    {
      exact validity,
    },
  },
  cases rin,
  {
    -- could match only at the last position
    sorry,
    -- we have created one more part
  },
  change r ∈ (list.map wrap_grule g₀.rules) at rin,
  rw list.mem_map at rin,
  rcases rin with ⟨r₀, rin₀, r_from_r₀⟩,
  -- could match anywhere except for possible `none` for spawning new parts at the end
  sorry,
end

private lemma in_language_star_of_in_star_grammar {g₀ : grammar T} {w : list T}
    (h : grammar_generates (star_grammar g₀) w) :
  w ∈ (grammar_language g₀).star :=
begin
  unfold grammar_generates at h,
  unfold language.star,
  rw set.mem_set_of_eq,
  unfold grammar_language,

  rcases big_induction (list.map symbol.terminal w) h with ⟨ parts, joined, each_part_in_lang ⟩,
  cases joined, swap,
  {
    exfalso,
    have last_symb := congr_arg (λ l : list (symbol T (star_grammar g₀).nt), l.reverse.nth 0) joined,
    clear_except last_symb,
    simp only [list.nth, list.reverse_append, list.reverse_singleton, list.singleton_append] at last_symb,
    have none_in_that := list.nth_mem last_symb,
    clear last_symb,
    rw list.mem_reverse at none_in_that,
    rw list.mem_map at none_in_that,
    rcases none_in_that with ⟨a, -, contradic⟩,
    tauto,
  },

  use list.map (list.filter_map oT_of_sTN) parts,
  split,
  {
    clear_except joined,
    have remapped := congr_arg (list.filter_map oT_of_sTN) joined,
    convert remapped,
    {
      symmetry,
      rw list.filter_map_map,
      convert_to list.filter_map option.some w = w,
      apply list.filter_map_some,
    },
    {
      rw list.filter_map_join,
      rw list.map_map,
      congr,
      ext1,
      induction x,
      {
        refl,
      },
      cases x_hd with t n,
      {
        rw function.comp_app,
        unfold list.map,
        unfold wrap_symbol,
        have convt : oT_of_sTN (@symbol.terminal T g₀.nt t) = some t := rfl,
        rw list.filter_map_cons_some _ _ _ convt,
        rw x_ih,
        refl,
      },
      {
        rw function.comp_app,
        unfold list.map,
        unfold wrap_symbol,
        rw list.filter_map_cons_none,
        swap, refl,
        rw list.filter_map_cons_none,
        swap, refl,
        rw x_ih,
      },
    },
  },
  {
    clear_except each_part_in_lang joined,
    intros w hw,
    rw list.mem_map at hw,
    rcases hw with ⟨ Z, Zin, w_as_lfmZ ⟩,
    rw set.mem_set_of_eq,
    unfold grammar_generates,
    have this_part_in_lang := each_part_in_lang Z Zin,
    convert this_part_in_lang,

    have z_as_terminal : ∀ z ∈ Z, ∃ t : T, symbol.terminal t = z,
    {
      intros z zin,
      clear_except joined zin Zin,
      have Z_as_list_of_terminals : ∃ l : list T, list.map symbol.terminal l = Z,
      {
        have parts_as_list_of_list_of_terminals : ∃ s : list (list T), list.map (list.map symbol.terminal) s = parts,
        {
          clear_except joined,
          have only_terminals : ∀ part ∈ parts, ∀ x ∈ part, ∃ t : T, x = symbol.terminal t,
          {
            intros p pinp,
            by_contradiction contra,
            push_neg at contra,
            rcases contra with ⟨s, sinp, counterexampl⟩,
            have impossible := congr_arg (λ l, wrap_symbol s ∈ l) joined,
            change
                (wrap_symbol s ∈ (list.map symbol.terminal w)) =
                (wrap_symbol s ∈ (list.join (list.map (list.map wrap_symbol) parts)))
              at impossible,
            have rightrue : (wrap_symbol s ∈ (list.join (list.map (list.map wrap_symbol) parts))) = true,
            {
              simp only [eq_iff_iff, iff_true],
              rw list.mem_join,
              use list.map wrap_symbol p,
              split,
              {
                clear_except pinp,
                exact list.mem_map_of_mem (list.map wrap_symbol) pinp,
              },
              {
                clear_except sinp,
                exact list.mem_map_of_mem wrap_symbol sinp,
              },
            },
            rw rightrue at impossible,
            rw list.mem_map at impossible,
            simp only [eq_iff_iff, iff_true] at impossible,
            rcases impossible with ⟨t, -, problema⟩,
            specialize counterexampl t,
            cases s,
            {
              unfold wrap_symbol at problema,
              apply counterexampl,
              rw symbol.terminal.inj_eq at problema ⊢,
              exact problema.symm,
            },
            rw ← joined at rightrue,
            simp only [eq_iff_iff, iff_true] at rightrue,
            rw list.mem_map at rightrue,
            rcases rightrue with ⟨t, -, contr⟩,
            unfold wrap_symbol at contr,
            clear_except contr,
            tauto,
          },
          use list.map (list.filter_map oT_of_sTN) parts,
          rw list.map_map,
          clear_except only_terminals,
          induction parts,
          {
            refl,
          },
          rw list.map,
          rw parts_ih (by {
            intros p pinpt,
            exact only_terminals p (list.mem_cons_of_mem parts_hd pinpt),
          }),
          congr,
          specialize only_terminals parts_hd (list.mem_cons_self parts_hd _),
          induction parts_hd,
          {
            refl,
          },
          specialize parts_hd_ih (by {
            intros x xinpht,
            exact only_terminals x (list.mem_cons_of_mem parts_hd_hd xinpht),
          }),
          cases only_terminals parts_hd_hd (list.mem_cons_self parts_hd_hd _) with t ht,
          rw ht,
          convert_to
            list.map symbol.terminal (t :: list.filter_map oT_of_sTN parts_hd_tl) =
            symbol.terminal t :: parts_hd_tl,
          simp,
          exact parts_hd_ih,
        },
        cases parts_as_list_of_list_of_terminals with s parts_from_s,
        rw ← parts_from_s at Zin,
        rw list.mem_map at Zin,
        rcases Zin with ⟨ l, -, foo ⟩,
        use l,
        exact foo,
      },
      cases Z_as_list_of_terminals with l Z_from_l,
      rw ← Z_from_l at zin,
      rw list.mem_map at zin,
      rcases zin with ⟨ t, -, bar ⟩,
      use t,
      exact bar,
    },
    rw ← w_as_lfmZ,
    clear_except z_as_terminal,

    induction Z with d l ih,
    {
      refl,
    },
    have d_as_terminal := z_as_terminal d (list.mem_cons_self d l),
    cases d_as_terminal with t stt_eq_d,
    rw ← stt_eq_d,
    have convt : oT_of_sTN (@symbol.terminal T g₀.nt t) = some t := rfl,
    rw list.filter_map_cons_some _ _ _ convt,
    rw list.map,
    congr,
    apply ih,
    intros z zin,
    apply z_as_terminal z,
    apply list.mem_cons_of_mem,
    exact zin,
  },
end

end difficult_direction


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨ g₀, hg₀ ⟩,
  use star_grammar g₀,
  rw ← hg₀,
  ext1 w,
  split,
  {
    exact in_language_star_of_in_star_grammar,
  },
  {
    exact in_star_grammar_of_in_language_star,
  },
end
