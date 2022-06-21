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
end


section difficult_direction

private def oT_of_sTN {g : grammar T} : symbol T g.nt → option T
| (symbol.terminal t) := some t
| (symbol.nonterminal _) := none

private lemma in_language_star_of_in_star_grammar {g₀ : grammar T} {w : list T}
    (h : grammar_generates (star_grammar g₀) w) :
  w ∈ (grammar_language g₀).star :=
begin
  unfold grammar_generates at h,
  unfold language.star,
  rw set.mem_set_of_eq,
  unfold grammar_language,

  have big_induction :
    ∀ v : list (symbol T (star_grammar g₀).nt),
      grammar_derives (star_grammar g₀) [symbol.nonterminal (star_grammar g₀).initial] v →
        ∃ (S : list (list (symbol T g₀.nt))), v = (list.map (list.map wrap_symbol) S).join ∧
        ∀ (u : list (symbol T g₀.nt)), u ∈ S → grammar_derives g₀ [symbol.nonterminal g₀.initial] u,
  {
    intros v gdv,
    sorry,
  },
  rcases big_induction _ h with ⟨ parts, joined, each_part_in_lang ⟩,
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
      -- TODO clean up after finishing
      intros z zin,
      clear_except joined zin Zin,
      rcases list.nth_le_of_mem zin with ⟨ n₁, hn₁, z_as_n₁th ⟩,
      rcases list.nth_le_of_mem Zin with ⟨ n₂, hn₂, Z_as_n₂th ⟩,
      have pomoc : ∃ l : list T, list.map symbol.terminal l = Z,
      {
        sorry,
      },
      cases pomoc with l pomocne,
      use l.nth_le n₁ (by {
        have pom_len := congr_arg list.length pomocne,
        rw list.length_map at pom_len,
        rw pom_len,
        exact hn₁,
      }),
      rw ← z_as_n₁th,
      have hurdurr := congr_arg (λ lis, list.nth_le lis n₁ sorry) pomocne,
      simp at hurdurr,
      exact hurdurr,
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
  clear hg₀,
  ext1 w,
  split,
  {
    exact in_language_star_of_in_star_grammar,
  },
  {
    exact in_star_grammar_of_in_language_star,
  },
end
