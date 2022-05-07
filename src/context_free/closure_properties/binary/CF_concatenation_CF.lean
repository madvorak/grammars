import context_free.cfgLiftSink


variable {T : Type}

private def combined_grammar (gₗ gᵣ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk
  (option (gₗ.nt ⊕ gᵣ.nt))
  none
  ((none, [
    symbol.nonterminal (some (sum.inl (gₗ.initial))),
    symbol.nonterminal (some (sum.inr (gᵣ.initial)))
  ]) :: (
    (list.map rule_of_rule₁ gₗ.rules) ++ (list.map rule_of_rule₂ gᵣ.rules)
  ))

/-- similar to `sink_symbol` -/
private def oN₁_of_N {g₁ g₂ : CF_grammar T} : (combined_grammar g₁ g₂).nt → (option g₁.nt)
| none := none
| (some (sum.inl nt)) := some nt
| (some (sum.inr _)) := none

/-- similar to `sink_symbol` -/
private def oN₂_of_N {g₁ g₂ : CF_grammar T} : (combined_grammar g₁ g₂).nt → (option g₂.nt)
| none := none
| (some (sum.inl _)) := none
| (some (sum.inr nt)) := some nt


private def g₁g (g₁ g₂ : CF_grammar T) : @lifted_grammar T :=
lifted_grammar.mk g₁ (combined_grammar g₁ g₂) (some ∘ sum.inl) (by {
  -- prove `function.injective (some ∘ sum.inl)` here
  intros x y h,
  apply sum.inl_injective,
  apply option.some_injective,
  exact h,
}) (by {
  -- prove `∀ r ∈ g₁.rules` we have `lift_rule (some ∘ sum.inl) r ∈ list.map rule_of_rule₁ g₁.rules` here
  intros r h,
  apply list.mem_cons_of_mem,
  apply list.mem_append_left,
  rw list.mem_map,
  use r,
  split,
  {
    exact h,
  },
  unfold rule_of_rule₁,
  unfold lift_rule,
  norm_num,
  unfold lift_string,
  unfold lsTN_of_lsTN₁,
  five_steps,
}) (by {
  intro r,
  rintro ⟨ r_in, r_ntype ⟩,
  cases r_in,
  {
    exfalso,
    rw r_in at r_ntype,
    dsimp at r_ntype,
    tauto,
  },
  change r ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at r_in,
  rw list.mem_append at r_in,
  cases r_in,
  {
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₁, r₁_in, r₁_convert_r ⟩,
    use r₁,
    split,
    {
      exact r₁_in,
    },
    rw ← r₁_convert_r,
    simp only [ lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁,
                prod.mk.inj_iff, eq_self_iff_true, true_and ],
    five_steps,
  },
  {
    exfalso,
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₂, r₂_in, r₂_convert_r ⟩,
    rw ← r₂_convert_r at r_ntype,
    unfold rule_of_rule₂ at r_ntype,
    dsimp at r_ntype,
    cases r_ntype with n₁ contr,
    rw option.some_inj at contr,
    tauto,
  },
}) oN₁_of_N (by {
  intros x y h,
  cases x,
  {
    right,
    refl,
  },
  cases x, swap,
  {
    right,
    refl,
  },
  cases y,
  {
    tauto,
  },
  cases y, swap,
  {
    tauto,
  },
  left,
  simp only [oN₁_of_N] at h,
  apply congr_arg,
  apply congr_arg,
  exact h,
}) (by { intro, refl })

private def g₂g (g₁ g₂ : CF_grammar T) : @lifted_grammar T :=
lifted_grammar.mk g₂ (combined_grammar g₁ g₂) (some ∘ sum.inr) (by {
  -- prove `function.injective (some ∘ sum.inl)` here
  intros x y h,
  apply sum.inr_injective,
  apply option.some_injective,
  exact h,
}) (by {
  -- prove `∀ r ∈ g₂.rules` we have `lift_rule (some ∘ sum.inr) r ∈ list.map rule_of_rule₂ g₂.rules` here
  intros r h,
  apply list.mem_cons_of_mem,
  apply list.mem_append_right,
  rw list.mem_map,
  use r,
  split,
  {
    exact h,
  },
  unfold rule_of_rule₂,
  unfold lift_rule,
  norm_num,
  unfold lift_string,
  unfold lsTN_of_lsTN₂,
  five_steps,
}) (by {
  intro r,
  rintro ⟨ r_in, r_ntype ⟩,
  cases r_in,
  {
    exfalso,
    rw r_in at r_ntype,
    dsimp at r_ntype,
    tauto,
  },
  change r ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at r_in,
  rw list.mem_append at r_in,
  cases r_in,
  {
    exfalso,
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₁, r₁_in, r₁_convert_r ⟩,
    rw ← r₁_convert_r at r_ntype,
    unfold rule_of_rule₁ at r_ntype,
    dsimp at r_ntype,
    cases r_ntype with n₂ contr,
    rw option.some_inj at contr,
    tauto,
  },
  {
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₂, r₂_in, r₂_convert_r ⟩,
    use r₂,
    split,
    {
      exact r₂_in,
    },
    rw ← r₂_convert_r,
    simp only [ lift_rule, rule_of_rule₂, lift_string, lsTN_of_lsTN₂,
                prod.mk.inj_iff, eq_self_iff_true, true_and ],
    five_steps,
  },
}) oN₂_of_N (by {
  intros x y h,
  cases x,
  {
    right,
    refl,
  },
  cases x,
  {
    right,
    refl,
  },
  cases y,
  {
    tauto,
  },
  cases y,
  {
    tauto,
  },
  left,
  simp only [oN₂_of_N] at h,
  apply congr_arg,
  apply congr_arg,
  exact h,
}) (by { intro, refl })


private def oT_of_sTN₃ {g₃ : CF_grammar T} : symbol T g₃.nt → option T
| (symbol.terminal t) := some t
| (symbol.nonterminal _) := none

private def liT_of_lsTN₃ {g₃ : CF_grammar T} : list (symbol T g₃.nt) → list T :=
list.filter_map oT_of_sTN₃

private lemma u_eq_take_map_w
    {g₁ g₂ : CF_grammar T}
    (u : list (symbol T g₁.nt))
    (v : list (symbol T g₂.nt))
    (w : list T)
    (len : u.length ≤ w.length)
    (hyp : list.take u.length (list.map sTN_of_sTN₁ u ++ lsTN_of_lsTN₂ v) =
           list.take u.length (list.map symbol.terminal w)) :
  u = list.take u.length (list.map symbol.terminal w) :=
begin
  ext1,
  by_cases n < u.length,
  {
    have ass : list.map sTN_of_sTN₁ u = list.take u.length (list.map symbol.terminal w),
    {
      convert hyp,
      have takenl := list.take_left (list.map sTN_of_sTN₁ u) (lsTN_of_lsTN₂ v),
      rw list.length_map at takenl,
      exact takenl.symm,
    },
    have nth_equ := congr_fun (congr_arg list.nth ass) n,
    rw list.nth_take h,
    rw list.nth_take h at nth_equ,
    have h' : n < w.length,
    {
      exact gt_of_ge_of_gt len h,
    },
    have triv : n < (list.map sTN_of_sTN₁ u).length,
    {
      rw list.length_map,
      exact h,
    },
    have trig : n < (list.map (@symbol.terminal T g₁.nt) w).length,
    {
      rw list.length_map,
      exact h',
    },
    have trin : n < (list.map (@symbol.terminal T (option (g₁.nt ⊕ g₂.nt))) w).length,
    {
      rw list.length_map,
      exact h',
    },
    rw list.nth_le_nth triv at nth_equ,
    rw list.nth_le_nth trin at nth_equ,
    rw option.some_inj at nth_equ,
    rw list.nth_le_map at nth_equ,
    swap, exact h,
    rw list.nth_le_map at nth_equ,
    swap, exact h',
    rw list.nth_le_nth,
    swap, exact h,
    rw list.nth_le_nth,
    swap, exact trig,
    apply congr_arg,
    norm_num,
    cases u.nth_le n h with termi nonte,
    {
      unfold sTN_of_sTN₁ at nth_equ,
      finish,
    },
    {
      exfalso,
      tauto,
    },
  },
  convert_to none = none,
  {
    finish,
  },
  {
    finish,
  },
  refl,
end

private lemma v_eq_drop_map_w
    {g₁ g₂ : CF_grammar T}
    (u : list (symbol T g₁.nt))
    (v : list (symbol T g₂.nt))
    (w : list T)
    (total_len : u.length + v.length = w.length)
    (hyp : list.drop u.length (list.map sTN_of_sTN₁ u ++ list.map sTN_of_sTN₂ v) =
           list.drop u.length (list.map symbol.terminal w)) :
  v = list.drop u.length (list.map symbol.terminal w) :=
begin
  ext1,
  by_cases n < v.length,
  {
    have nth_equ := congr_fun (congr_arg list.nth hyp) n,
    rw list.nth_drop,
    rw list.nth_drop at nth_equ,
    rw list.nth_drop at nth_equ,

    have hunltuv : u.length + n < u.length + v.length,
    {
      apply add_lt_add_left h,
    },
    have hunltw : u.length + n < w.length,
    {
      rw ← total_len,
      exact hunltuv,
    },
    have hlen₁ : u.length + n < (list.map sTN_of_sTN₁ u ++ list.map sTN_of_sTN₂ v).length,
    {
      rw list.length_append,
      rw list.length_map,
      rw list.length_map,
      exact hunltuv,
    },
    have hlen₂ : u.length + n < (list.map (@symbol.terminal T (option (g₁.nt ⊕ g₂.nt))) w).length,
    {
      rw list.length_map,
      exact hunltw,
    },
    have hlen₂' : u.length + n < (list.map (@symbol.terminal T g₂.nt) w).length,
    {
      rw list.length_map,
      exact hunltw,
    },
    rw list.nth_le_nth hlen₁ at nth_equ,
    rw list.nth_le_nth hlen₂ at nth_equ,
    rw list.nth_le_nth h,
    rw list.nth_le_nth hlen₂',

    rw option.some_inj at *,
    have hlen₀ : (list.map sTN_of_sTN₁ u).length ≤ u.length + n,
    {
      rw list.length_map,
      exact le_self_add,
    },
    have hlen : n < (list.map (@sTN_of_sTN₂ T g₁ g₂) v).length,
    {
      rw list.length_map,
      exact h,
    },
    have nth_equ_simplified :
      (list.map sTN_of_sTN₂ v).nth_le n hlen =
      (list.map symbol.terminal w).nth_le (u.length + n) hlen₂,
    {
      rw list.nth_le_append_right hlen₀ at nth_equ,
      convert nth_equ,
      rw list.length_map,
      symmetry,
      apply add_tsub_cancel_left,
    },
    rw list.nth_le_map at nth_equ_simplified,

    cases v.nth_le n h with x,
    {
      unfold sTN_of_sTN₂ at nth_equ_simplified,
      rw list.nth_le_map _ _ hunltw at nth_equ_simplified,
      rw list.nth_le_map _ _ hunltw,
      injection nth_equ_simplified with hx,
      apply congr_arg,
      exact hx,
    },
    {
      exfalso,
      clear_except nth_equ_simplified,
      finish,
    },
  },
  convert_to none = none,
  {
    finish,
  },
  {
    rw list.nth_drop,
    push_neg at h,
    rw list.nth_eq_none_iff,
    rw list.length_map,
    rw ← total_len,
    apply add_le_add_left h,
  },
  refl,
end

private def sTN₁_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (option (g₁.nt ⊕ g₂.nt)) → option (symbol T g₁.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := option.map symbol.nonterminal (oN₁_of_N nont)

private def sTN₂_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (option (g₁.nt ⊕ g₂.nt)) → option (symbol T g₂.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := option.map symbol.nonterminal (oN₂_of_N nont)

private def lsTN₁_of_lsTN {g₁ g₂ : CF_grammar T} (lis : list (symbol T (option (g₁.nt ⊕ g₂.nt)))) :
  list (symbol T g₁.nt) :=
list.filter_map sTN₁_of_sTN lis

private def lsTN₂_of_lsTN {g₁ g₂ : CF_grammar T} (lis : list (symbol T (option (g₁.nt ⊕ g₂.nt)))) :
  list (symbol T g₂.nt) :=
list.filter_map sTN₂_of_sTN lis

private lemma self_of_sTN₁ {g₁ g₂ : CF_grammar T} (symb : symbol T g₁.nt) :
  sTN₁_of_sTN (@sTN_of_sTN₁ _ _ g₂ symb) = symb :=
begin
  cases symb;
  finish,
end

private lemma self_of_sTN₂ {g₁ g₂ : CF_grammar T} (symb : symbol T g₂.nt) :
  sTN₂_of_sTN (@sTN_of_sTN₂ _ g₁ _ symb) = symb :=
begin
  cases symb;
  finish,
end

private lemma self_of_lsTN₁ {g₁ g₂ : CF_grammar T} (stri : list (symbol T g₁.nt)) :
  lsTN₁_of_lsTN (@lsTN_of_lsTN₁ _ _ g₂ stri) = stri :=
begin
  unfold lsTN_of_lsTN₁,
  unfold lsTN₁_of_lsTN,
  rw list.filter_map_map,
  change list.filter_map (λ x, sTN₁_of_sTN (sTN_of_sTN₁ x)) stri = stri,
  convert_to list.filter_map (λ x, some x) stri = stri,
  {
    have equal_functions : (λ (x : symbol T g₁.nt), sTN₁_of_sTN (sTN_of_sTN₁ x)) = (λ x, some x),
    {
      ext1,
      apply self_of_sTN₁,
    },
    rw ← equal_functions,
    apply congr_fun,
    apply congr_arg,
    ext1,
    apply congr_fun,
    refl,
  },
  finish,
end

private lemma self_of_lsTN₂ {g₁ g₂ : CF_grammar T} (stri : list (symbol T g₂.nt)) :
  lsTN₂_of_lsTN (@lsTN_of_lsTN₂ _ g₁ _ stri) = stri :=
begin
  unfold lsTN_of_lsTN₂,
  unfold lsTN₂_of_lsTN,
  rw list.filter_map_map,
  change list.filter_map (λ x, sTN₂_of_sTN (sTN_of_sTN₂ x)) stri = stri,
  convert_to list.filter_map (λ x, some x) stri = stri,
  {
    have equal_functions : (λ (x : symbol T g₂.nt), sTN₂_of_sTN (sTN_of_sTN₂ x)) = (λ x, some x),
    {
      ext1,
      apply self_of_sTN₂,
    },
    rw ← equal_functions,
    apply congr_fun,
    apply congr_arg,
    ext1,
    apply congr_fun,
    refl,
  },
  finish,
end

private lemma in_language_combi
    {g₁ g₂ : CF_grammar T}
    {w : list T}
    (hyp : w ∈ CF_language (combined_grammar g₁ g₂)) :
  w ∈ CF_language g₁ * CF_language g₂ :=
begin
  rw language.mem_mul,
  change
    CF_derives
      (combined_grammar g₁ g₂)
      [symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (list.map symbol.terminal w) at hyp,

  cases CF_tran_or_id_of_deri hyp,
  {
    rename h refl_contr,
    exfalso,
    have hh := congr_fun (congr_arg list.nth refl_contr) 0,
    dsimp at hh,
    
    by_cases (list.map symbol.terminal w).length = 0,
    {
      have empty_none : (list.map symbol.terminal w).nth 0 = none,
      {
        finish,
      },
      rw empty_none at hh,
      tauto,
    },
    rw list.nth_map at hh,
    have hw0 : ∃ s, w.nth 0 = some s,
    {
      cases w.nth 0,
      {
        exfalso,
        dsimp at hh,
        tauto,
      },
      use val,
    },
    rcases hw0 with ⟨ s, hs ⟩,
    rw hs at hh,
    dsimp at hh,
    rw option.some_inj at hh,
    tauto,
    exact T,
  },
  rcases h with ⟨ y, first_step, derivation ⟩,
  clear hyp,

  have only_option :
    y =
    [
      symbol.nonterminal (some (sum.inl (g₁.initial))),
      symbol.nonterminal (some (sum.inr (g₂.initial)))
    ],
  {
    rcases first_step with ⟨ first_rule, first_rule_in, p, q, bef, aft ⟩,
    have len_bef := congr_arg list.length bef,
    simp at len_bef,
    have p_nil : p = [],
    {
      have p0 : p.length = 0,
      {
        linarith,
      },
      rw list.length_eq_zero at p0,
      exact p0,
    },
    have q_nil : q = [],
    {
      have q0 : q.length = 0,
      {
        linarith,
      },
      rw list.length_eq_zero at q0,
      exact q0,
    },
    have initial : first_rule.fst = none,
    {
      apply symbol.nonterminal.inj,
      rw p_nil at bef,
      rw q_nil at bef,
      rw list.append_nil at bef,
      rw list.nil_append at bef,
      exact list.head_eq_of_cons_eq (eq.symm bef),
    },
    have only_rule :
      first_rule = (none, [
        symbol.nonterminal (some (sum.inl (g₁.initial))),
        symbol.nonterminal (some (sum.inr (g₂.initial)))
      ]),
    {
      change first_rule ∈ (
        (none, [
          symbol.nonterminal (some (sum.inl (g₁.initial))),
          symbol.nonterminal (some (sum.inr (g₂.initial)))
        ]) :: (
          (list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules)
        )
      ) at first_rule_in,
      cases first_rule_in,
      {
        exact first_rule_in,
      },
      exfalso,
      change first_rule ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at first_rule_in,
      rw list.mem_append at first_rule_in,
      cases first_rule_in,
      {
        delta rule_of_rule₁ at first_rule_in,
        have rfst :
          first_rule.fst ∈ list.map prod.fst
            (list.map (
                λ (r : g₁.nt × list (symbol T g₁.nt)),
                (some (sum.inl r.fst), lsTN_of_lsTN₁ r.snd)
              ) g₁.rules),
        {
          exact list.mem_map_of_mem prod.fst first_rule_in,
        },
        rw initial at rfst,
        simp at rfst,
        exact rfst,
      },
      {
        delta rule_of_rule₂ at first_rule_in,
        have rfst :
          first_rule.fst ∈ list.map prod.fst
            (list.map (
                λ (r : g₂.nt × list (symbol T g₂.nt)),
                (some (sum.inr r.fst), lsTN_of_lsTN₂ r.snd)
              ) g₂.rules),
        {
          exact list.mem_map_of_mem prod.fst first_rule_in,
        },
        rw initial at rfst,
        simp at rfst,
        exact rfst,
      },
    },
    rw [ p_nil, q_nil, only_rule ] at aft,
    rw list.append_nil at aft,
    rw list.nil_append at aft,
    exact aft,
  },
  clear first_step,
  rw only_option at derivation,
  clear only_option y,

  have complicated_induction :
    ∀ x : list (symbol T (combined_grammar g₁ g₂).nt),
      CF_derives
        (combined_grammar g₁ g₂)
        [
          symbol.nonterminal (some (sum.inl (g₁.initial))),
          symbol.nonterminal (some (sum.inr (g₂.initial)))
        ]
        x →
        ∃ u : list (symbol T g₁.nt), ∃ v : list (symbol T g₂.nt), and
          (CF_derives g₁ [symbol.nonterminal g₁.initial] u)
          (CF_derives g₂ [symbol.nonterminal g₂.initial] v)
          ∧ (lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v = x),
  {
    intros x ass,
    induction ass with a b trash orig ih,
    {
      use [[symbol.nonterminal g₁.initial], [symbol.nonterminal g₂.initial]],
      split,
      {
        split;
        apply CF_deri_self,
      },
      {
        refl,
      },
    },
    clear trash,
    rcases orig with ⟨ orig_rule, orig_in, c, d, bef, aft ⟩,
    rcases ih with ⟨ u, v, ⟨ ih₁, ih₂ ⟩, ih_concat ⟩,
    cases orig_in,
    {
      exfalso,
      rw ← ih_concat at bef,
      rw orig_in at bef,
      clear_except bef,
      dsimp at bef,
      have init_nt_in_bef_right : symbol.nonterminal none ∈ c ++ [symbol.nonterminal none] ++ d,
      {
        apply list.mem_append_left,
        apply list.mem_append_right,
        apply list.mem_singleton_self,
      },
      have init_nt_notin_bef_left : symbol.nonterminal none ∉ lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v,
      {
        rw list.mem_append,
        push_neg,
        split,
        {
          rw list.mem_iff_nth_le,
          push_neg,
          unfold lsTN_of_lsTN₁,
          intros n hn,
          rw list.nth_le_map,
          {
            cases u.nth_le n _ with t s,
            {
              tauto,
            },
            {
              unfold sTN_of_sTN₁,
              intro hypo,
              have impossible := symbol.nonterminal.inj hypo,
              clear_except impossible,
              tauto,
            },
          },
          {
            rw list.length_map at hn,
            exact hn,
          },
        },
        {
          rw list.mem_iff_nth_le,
          push_neg,
          unfold lsTN_of_lsTN₂,
          intros n hn,
          rw list.nth_le_map,
          {
            cases v.nth_le n _ with t s,
            {
              tauto,
            },
            {
              unfold sTN_of_sTN₂,
              intro hypo,
              have impossible := symbol.nonterminal.inj hypo,
              clear_except impossible,
              tauto,
            },
          },
          {
            rw list.length_map at hn,
            exact hn,
          },
        },
      },
      rw bef at init_nt_notin_bef_left,
      exact init_nt_notin_bef_left init_nt_in_bef_right,
    },
    change orig_rule ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at orig_in,
    rw list.mem_append at orig_in,
    cases orig_in,
    {
      clear derivation w,
      -- nonterminal was rewritten in the left half of `a` ... upgrade `u`
      rw list.mem_map at orig_in,
      rcases orig_in with ⟨ r₁, r₁_in, r₁_conv ⟩,
      rw aft,
      rw bef at ih_concat,
      clear bef aft a b,
      rw ← r₁_conv,
      rw ← r₁_conv at ih_concat,
      clear r₁_conv orig_rule,
      -- now we need to split:
      -- `lsTN_of_lsTN₁ u = c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d`.beginning
      -- `lsTN_of_lsTN₂ v = d`.remaining part
      have part_for_u := congr_arg (list.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat,
      have part_for_v := congr_arg (list.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat,
      rw list.take_left at part_for_u,
      rw list.drop_left at part_for_v,
      -- TODO here TODO

      have h_len : (@lsTN_of_lsTN₁ T g₁ g₂ u).length > c.length,
      {
        by_contradiction contra,
        push_neg at contra,

        have not_in : symbol.nonterminal (rule_of_rule₁ r₁).fst ∉ lsTN_of_lsTN₂ v,
        {
          unfold lsTN_of_lsTN₂,
          rw list.mem_map,
          rintro ⟨ s, trash, imposs ⟩,
          cases s,
          {
            have terminal_eq_nonte : symbol.terminal s = symbol.nonterminal (some (sum.inl r₁.fst)),
            {
              exact imposs,
            },
            clear_except terminal_eq_nonte,
            tauto,
          },
          {
            have ntinr_eq_ntinl : symbol.nonterminal (some (sum.inr s)) = symbol.nonterminal (some (sum.inl r₁.fst)),
            {
              exact imposs,
            },
            have inr_eq_inl := option.some.inj (symbol.nonterminal.inj ntinr_eq_ntinl),
            clear_except inr_eq_inl,
            tauto,
          },
        },

        have yes_in : symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst ∈ lsTN_of_lsTN₂ v,
        {
          have lcth := congr_fun (congr_arg list.nth ih_concat) c.length,
          rw list.append_assoc c at lcth,
          have clength :
            (c ++ ([symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d)).nth c.length =
            some (symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst),
          {
            rw list.nth_append_right, swap,
            {
              refl,
            },
            rw nat.sub_self,
            refl,
          },
          rw clength at lcth,
          rw list.nth_append_right contra at lcth,
          exact list.nth_mem lcth,
        },

        exact not_in yes_in,
      },
      
      let d' : list (symbol T (combined_grammar g₁ g₂).nt) :=
        list.take ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d,
      let u' := lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ d'),
      use u',
      use v,
      split,
      {
        split,
        {
          change
            CF_derives g₁ [symbol.nonterminal g₁.initial] (lsTN₁_of_lsTN (
              c ++ (rule_of_rule₁ r₁).snd ++
              (list.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d)
            )),
          apply CF_deri_of_deri_tran ih₁,
          convert_to
            CF_transforms
              g₁
              (lsTN₁_of_lsTN (
                list.take (lsTN_of_lsTN₁ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d)
              ))
              (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ list.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d)),
          {
            rw ← part_for_u,
            rw self_of_lsTN₁,
          },
          use r₁,
          split,
          {
            exact r₁_in,
          },
          use lsTN₁_of_lsTN c,
          use lsTN₁_of_lsTN (list.take (u.length - (c.length + 1)) d),
          split,
          {
            convert_to
              lsTN₁_of_lsTN (
                c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                  (list.take (u.length - (c.length + 1)) d)
              ) =
              lsTN₁_of_lsTN c ++ [symbol.nonterminal r₁.fst] ++
                lsTN₁_of_lsTN (list.take (u.length - (c.length + 1)) d),
            {
              apply congr_arg,
              have trivi_len : (lsTN_of_lsTN₁ u).length = u.length,
              {
                unfold lsTN_of_lsTN₁,
                rw list.length_map,
              },
              rw trivi_len,
              have another_trivi_len : c.length + 1 = (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length,
              {
                rw list.length_append,
                rw list.length_singleton,
              },
              rw another_trivi_len,

              have borrow_and_return : u.length =
                (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                  (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length),
              {
                symmetry,
                clear_except h_len,
                apply nat.add_sub_of_le,
                rw list.length_append,
                rw list.length_singleton,
                unfold lsTN_of_lsTN₁ at h_len,
                rw list.length_map at h_len,
                rw nat.succ_le_iff,
                exact h_len,
              },
              convert_to
                list.take
                  ((c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                    (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length))
                  (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
                c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                  list.take (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length) d,
              {
                apply congr_fun,
                apply congr_arg,
                exact borrow_and_return,
              },
              rw list.take_append,
            },
            unfold lsTN₁_of_lsTN,
            rw list_filter_map_append_append,
            refl,
          },
          {
            convert_to
              lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ (list.take (u.length - (c.length + 1)) d)) =
              lsTN₁_of_lsTN c ++ r₁.snd ++ lsTN₁_of_lsTN (list.take (u.length - (c.length + 1)) d),
            {
              apply congr_arg,
              apply congr_arg2,
              {
                refl,
              },
              unfold lsTN_of_lsTN₁,
              rw list.length_map,
            },
            unfold lsTN₁_of_lsTN,
            rw list_filter_map_append_append,
            change
              list.filter_map sTN₁_of_sTN c ++ lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd) ++
                list.filter_map sTN₁_of_sTN (list.take (u.length - (c.length + 1)) d) =
              list.filter_map sTN₁_of_sTN c ++ r₁.snd ++
                list.filter_map sTN₁_of_sTN (list.take (u.length - (c.length + 1)) d),
            rw self_of_lsTN₁,
          },
        },
        {
          exact ih₂,
        },
      },
      {
        have trivi_min :
          min ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d.length =
          (@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1),
        {
          apply min_eq_left,
          unfold lsTN_of_lsTN₁,
          rw list.length_map,
          clear_except part_for_u,
          unfold lsTN_of_lsTN₁ at part_for_u,
          have lens := congr_arg list.length part_for_u,
          rw list.length_map at lens,
          rw list.length_take at lens,
          rw list.length_append at lens,
          rw list.length_append at lens,
          rw list.length_singleton at lens,
          have uleng_le : u.length ≤ c.length + 1 + d.length,
          {
            rw ← min_eq_left_iff,
            exact lens.symm,
          },
          clear_except uleng_le,
          omega,
        },

        have c_converted_and_back : list.map sTN_of_sTN₁ (list.filter_map sTN₁_of_sTN c) = c,
        {
          /-
            Simplified schema of this conversion (applies to some other conversions, too):
            we have `g ∘ f = id` but `f ∘ g` does not annihilate (in general)
            we need `f(g(c)) = c` for a specific `c`
            which we can express as `c = f(x)` and then we calculate
            `f(g(c)) = f(g(f(x))) = f(x) = c` hooray!
          -/
          have taken_c_from_u := congr_arg (list.take c.length) part_for_u,
          rw list.take_take at taken_c_from_u,
          rw min_eq_left (le_of_lt h_len) at taken_c_from_u,
          rw list.append_assoc at taken_c_from_u,
          rw list.take_left at taken_c_from_u,
          convert_to list.map sTN_of_sTN₁ (list.filter_map sTN₁_of_sTN (list.take c.length (lsTN_of_lsTN₁ u))) = c,
          {
            rw taken_c_from_u,
          },
          unfold lsTN_of_lsTN₁,
          rw ← list.map_take,
          change list.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ (list.take c.length u))) = _,
          rw self_of_lsTN₁,
          rw list.map_take,
          exact taken_c_from_u,
        },

        have d_converted_and_back :
          list.map sTN_of_sTN₁ (list.filter_map sTN₁_of_sTN (list.take (
            (list.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)
          ) d)) =
          list.take ((list.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)) d,
        {
          have taken_d_from_dropped_u := congr_arg (list.drop (c.length + 1)) part_for_u,
          have for_the_decomposition :
            (@lsTN_of_lsTN₁ T g₁ g₂ u).length =
            (c.length + 1) + ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)),
          {
            symmetry,
            apply nat.add_sub_of_le,
            exact nat.succ_le_of_lt h_len,
          },
          rw for_the_decomposition at taken_d_from_dropped_u,
          rw list.drop_take at taken_d_from_dropped_u,
          have translate_counts : c.length + 1 = (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length,
          {
            rw list.length_append,
            rw list.length_singleton,
          },
          rw translate_counts at taken_d_from_dropped_u,
          rw list_drop_length_append at taken_d_from_dropped_u,
          rw ← translate_counts at taken_d_from_dropped_u,
          change
            list.map sTN_of_sTN₁ (
              list.filter_map sTN₁_of_sTN (list.take ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d)
            ) = _,
          rw ← taken_d_from_dropped_u,
          change list.map sTN_of_sTN₁ (lsTN₁_of_lsTN (list.drop (c.length + 1) (list.map sTN_of_sTN₁ u))) = _,
          rw ← list.map_drop,
          change list.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ (list.drop (c.length + 1) u))) = _,
          rw self_of_lsTN₁,
          rw list.map_drop,
          exact taken_d_from_dropped_u,
        },

        have len_u' : u'.length = c.length + (@rule_of_rule₁ T g₁ g₂ r₁).snd.length + d'.length,
        {
          change
            (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ d')).length =
            c.length + (rule_of_rule₁ r₁).snd.length + d'.length,
          unfold lsTN₁_of_lsTN,
          rw list_filter_map_append_append,
          convert_to
            (list.map sTN_of_sTN₁ (
              list.filter_map sTN₁_of_sTN c ++
              list.filter_map sTN₁_of_sTN (rule_of_rule₁ r₁).snd ++
              list.filter_map sTN₁_of_sTN d'
            )).length =
            c.length + (rule_of_rule₁ r₁).snd.length + d'.length,
          {
            rw list.length_map,
          },
          rw list_map_append_append,
          rw c_converted_and_back,
          change
            (c ++ _ ++ list.map sTN_of_sTN₁ (list.filter_map sTN₁_of_sTN (
              list.take ((list.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)) d
            ))).length = _,
          rw d_converted_and_back,
          change (c ++ list.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd)) ++ d').length = _,
          rw self_of_lsTN₁,
          rw list.length_append,
          rw list.length_append,
          refl,
        },

        have express_u'_as_crd :
          lsTN_of_lsTN₁ u' =
          list.take (@lsTN_of_lsTN₁ T g₁ g₂ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
        {
          change
            lsTN_of_lsTN₁ (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++
              (list.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d))) =
            list.take (lsTN_of_lsTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
          convert_to
            c ++ (rule_of_rule₁ r₁).snd ++ (list.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d) =
            list.take (lsTN_of_lsTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
          {
            unfold lsTN₁_of_lsTN,
            rw list_filter_map_append_append,
            unfold lsTN_of_lsTN₁,
            rw list_map_append_append,
            rw c_converted_and_back,
            rw d_converted_and_back,
            change c ++ list.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd)) ++ _ = _,
            rw self_of_lsTN₁,
            refl,
          },

          have len_add_sub :
            (@lsTN_of_lsTN₁ T g₁ g₂ u').length =
            (c ++ (rule_of_rule₁ r₁).snd).length +
              ((@lsTN_of_lsTN₁ T g₁ g₂ u').length - (c ++ (rule_of_rule₁ r₁).snd).length),
          {
            symmetry,
            apply nat.add_sub_of_le,
            unfold lsTN_of_lsTN₁,
            rw list.length_map,
            rw len_u',
            rw list.length_append,
            apply le_self_add,
          },
          rw len_add_sub,
          rw list.take_append,
          apply congr_arg2,
          {
            refl,
          },
          rw list.length_append,
          apply congr_arg2, swap,
          {
            refl,
          },
          unfold lsTN_of_lsTN₁,
          rw list.length_map,
          rw list.length_map,
          rw len_u',
          simp,
          rw trivi_min,
          unfold lsTN_of_lsTN₁,
          rw list.length_map,
        },
        rw express_u'_as_crd,

        have identity_of_suffixes :
          list.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
          list.drop (@lsTN_of_lsTN₁ T g₁ g₂ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
        {
          clear_except h_len trivi_min len_u',
          have h_len_ : (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length ≤ (@lsTN_of_lsTN₁ T g₁ g₂ u).length,
          {
            rw list.length_append,
            rw list.length_singleton,
            apply nat.succ_le_of_lt,
            exact h_len,
          },
          have intermediate :
            list.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
            list.drop ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d,
          {
            convert_to
              list.drop
                ((c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                  ((lsTN_of_lsTN₁ u).length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length))
                (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
              list.drop ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d,
            {
              symmetry,
              apply congr_arg2, swap,
              {
                refl,
              },
              apply nat.add_sub_of_le,
              exact h_len_,
            },
            rw list.drop_append,
            apply congr_arg2, swap,
            {
              refl,
            },
            rw list.length_append,
            rw list.length_singleton,
          },
          rw intermediate,
          change _ = list.drop (list.map sTN_of_sTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
          rw list.length_map,
          rw len_u',
          rw ← list.length_append,
          rw list.drop_append,
          rw list.length_take,
          rw trivi_min,
        },

        rw part_for_v,
        rw identity_of_suffixes,
        apply list.take_append_drop,
      },
    },
    {
      -- nonterminal was rewritten in the right half of `a` ... upgrade `v`
      use u,
      use list.nil, -- TODO change for upgraded `v`
      split,
      {
        split,
        {
          exact ih₁,
        },
        {
          sorry,
        },
      },
      {
        sorry,
      },
    },
  },
  specialize complicated_induction (list.map symbol.terminal w) derivation,

  rcases complicated_induction with ⟨ u, v, ⟨ hu, hv ⟩, hw ⟩,
  use liT_of_lsTN₃ u,
  use liT_of_lsTN₃ v,
  have huvw :
    @liT_of_lsTN₃ T
      (combined_grammar g₁ g₂)
      (lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v)
    = liT_of_lsTN₃ (list.map symbol.terminal w),
  {
    exact congr_arg liT_of_lsTN₃ hw,
  },
  split,
  {
    change CF_derives _ _ _,
    unfold liT_of_lsTN₃,
    convert hu,
    have u_from_terminals : ∃ uₜ : list T, u = list.map symbol.terminal uₜ,
    {
      unfold lsTN_of_lsTN₁ at hw,
      use list.take u.length w,
      rw list.map_take,
      exact u_eq_take_map_w u v w
        (by {
          have hwlen := congr_arg list.length hw,
          rw list.length_append at hwlen,
          rw list.length_map at hwlen,
          rw list.length_map at hwlen,
          exact nat.le.intro hwlen,
        }) (congr_arg (list.take u.length) hw),
    },
    cases u_from_terminals with uₜ hut,
    rw hut,
    rw list.filter_map_map,
    convert_to list.map symbol.terminal (list.filter_map some uₜ) = list.map symbol.terminal uₜ,
    rw list.filter_map_some,
  },
  split,
  {
    change CF_derives _ _ _,
    unfold liT_of_lsTN₃,
    convert hv,
    have v_from_terminals : ∃ vₜ : list T, v = list.map symbol.terminal vₜ,
    {
      unfold lsTN_of_lsTN₁ at hw,
      unfold lsTN_of_lsTN₂ at hw,
      use list.drop u.length w,
      rw list.map_drop,
      have hwlen := congr_arg list.length hw,
      rw list.length_append at hwlen,
      repeat { rw list.length_map at hwlen },
      exact v_eq_drop_map_w u v w hwlen (congr_arg (list.drop u.length) hw),
    },
    cases v_from_terminals with vₜ hvt,
    rw hvt,
    rw list.filter_map_map,
    convert_to list.map symbol.terminal (list.filter_map some vₜ) = list.map symbol.terminal vₜ,
    rw list.filter_map_some,
  },
  unfold liT_of_lsTN₃ at huvw,
  rw list.filter_map_append at huvw,
  unfold lsTN_of_lsTN₁ at huvw,
  unfold lsTN_of_lsTN₂ at huvw,
  repeat { rw list.filter_map_map at huvw },
  have disappear_sTN_of_sTN₁ : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ sTN_of_sTN₁ = oT_of_sTN₃,
  {
    ext1,
    cases x;
    refl,
  },
  have disappear_sTN_of_sTN₂ : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ sTN_of_sTN₂ = oT_of_sTN₃,
  {
    ext1,
    cases x;
    refl,
  },
  rw disappear_sTN_of_sTN₁ at huvw,
  rw disappear_sTN_of_sTN₂ at huvw,
  unfold liT_of_lsTN₃,
  convert huvw,
  have bundle_unbundle : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ symbol.terminal = option.some,
  {
    ext1,
    refl,
  },
  rw bundle_unbundle,
  rw list.filter_map_some,
end


private lemma in_language_conca
    {g₁ g₂ : CF_grammar T}
    {w : list T}
    (hyp : w ∈ CF_language g₁ * CF_language g₂) :
  w ∈ CF_language (combined_grammar g₁ g₂) :=
begin
  rw language.mem_mul at hyp,
  rcases hyp with ⟨ u, v, hu, hv, hw ⟩,
  unfold CF_language at *,
  change
    CF_derives
      (combined_grammar g₁ g₂)
      [symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (list.map symbol.terminal w),

  apply @CF_deri_of_tran_deri T
    (combined_grammar g₁ g₂)
    _ [
      symbol.nonterminal (some (sum.inl (g₁.initial))),
      symbol.nonterminal (some (sum.inr (g₂.initial)))
    ] _,
  {
    use (none, [
        symbol.nonterminal (some (sum.inl (g₁.initial))),
        symbol.nonterminal (some (sum.inr (g₂.initial)))
      ]),
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  rw ← hw,
  rw list.map_append,
  apply @CF_deri_of_deri_deri T
    (combined_grammar g₁ g₂) _
    (list.map symbol.terminal u ++ [symbol.nonterminal (some (sum.inr g₂.initial))]) _,
  {
    change
      CF_derives
        (combined_grammar g₁ g₂)
        ([symbol.nonterminal (some (sum.inl g₁.initial))] ++ [symbol.nonterminal (some (sum.inr g₂.initial))])
        (list.map symbol.terminal u ++ [symbol.nonterminal (some (sum.inr g₂.initial))]),
    apply CF_derives_with_postfix,

    change CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal u) at hu,
    let gg₁ := g₁g g₁ g₂,
    change CF_derives gg₁.g [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal u),
    
    have ini_equ :
      [symbol.nonterminal (some (sum.inl g₁.initial))] =
      list.map (lift_symbol gg₁.lift_nt) [symbol.nonterminal g₁.initial],
    {
      apply list.singleton_eq,
    },
    rw ini_equ,

    have baz : list.map symbol.terminal u = list.map (lift_symbol gg₁.lift_nt) (list.map symbol.terminal u),
    {
      rw list.map_map,
      apply congr_fun,
      apply congr_arg,
      refl,
    },
    rw baz,
    
    exact lift_deri gg₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal u) hu,
  },
  {
    apply CF_derives_with_prefix,

    change CF_derives g₂ [symbol.nonterminal g₂.initial] (list.map symbol.terminal v) at hv,
    let gg₂ := g₂g g₁ g₂,
    change CF_derives gg₂.g [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal v),
    
    have ini_equ :
      [symbol.nonterminal (some (sum.inr g₂.initial))] =
      list.map (lift_symbol gg₂.lift_nt) [symbol.nonterminal g₂.initial],
    {
      apply list.singleton_eq,
    },
    rw ini_equ,

    have baz : list.map symbol.terminal v = list.map (lift_symbol gg₂.lift_nt) (list.map symbol.terminal v),
    {
      rw list.map_map,
      apply congr_fun,
      apply congr_arg,
      refl,
    },
    rw baz,
    
    exact lift_deri gg₂ [symbol.nonterminal g₂.initial] (list.map symbol.terminal v) hv,
  },
end


/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

  use combined_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ * L₂ ⊇ ` here
    intros w hyp,
    rw ← h₁,
    rw ← h₂,
    exact in_language_combi hyp,
  },
  {
    -- prove `L₁ * L₂ ⊆ ` here
    intros w hyp,
    rw ← h₁ at hyp,
    rw ← h₂ at hyp,
    exact in_language_conca hyp,
  },
end
