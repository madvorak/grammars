import unrestricted.grammarLiftSink


variable {T : Type}

private def wrap_symbol {N : Type} : symbol T N → symbol T (option N)
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (option.some n)

private def wrap_grule {N : Type} (r : grule T N) : grule T (option N) :=
grule.mk
  (
    list.map wrap_symbol r.input_string.first,
    option.some r.input_string.secon,
    list.map wrap_symbol r.input_string.third
  )
  (list.map wrap_symbol r.output_string)

private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (option g.nt) none (
    (grule.mk ([], none, []) ([])) ::
    (grule.mk ([], none, []) ([symbol.nonterminal (option.some g.initial), symbol.nonterminal none])) ::
    (list.map wrap_grule g.rules)
  )

/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  intro ass,
  cases ass with g₀ hg₀,
  use star_grammar g₀,
  rw ← hg₀,
  ext1 w,
  split,
  {
    sorry,
  },
  {
    rintro ⟨ parts, joined, each_part_in_lang ⟩,
    unfold grammar_language,
    rw set.mem_set_of_eq,
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
        use grule.mk ([], none, []) ([symbol.nonterminal (option.some g₀.initial), symbol.nonterminal none]),
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
  },
end
