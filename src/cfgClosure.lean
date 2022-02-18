import cfg
import computability.DFA
import tactic


def is_Reg {T : Type} (L : language T) :=
∃ σ : Type, ∃ a : DFA T σ, a.accepts = L

def is_CF {T : Type} (L : language T) :=
∃ g : CF_grammar T, CF_language g = L



lemma CF_derives_reflexive {T : Type} {g : CF_grammar T} {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

lemma list_three_parts {T₁ T₂ : Type} {x y z : list T₁} {f : T₁ → T₂} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp

lemma unpack_transitive_closure {α : Type} {r : α → α → Prop} {x z : α}
  (h : relation.refl_trans_gen r x z) (nontriv : x ≠ z) :
    ∃ y : α, (r x y) ∧ (relation.refl_trans_gen r y z) :=
(relation.refl_trans_gen.cases_head h).resolve_left nontriv


theorem CF_under_union {T : Type} (L₁ : language T) (L₂ : language T) :
  ((is_CF L₁) ∧ (is_CF L₂))  →  (is_CF (L₁ + L₂)) :=
begin
  intro input,
  cases input with cf₁ cf₂,

  cases cf₁ with g₁ h₁,
  cases cf₂ with g₂ h₂,

  let N₁ : Type := g₁.nt,
  let N₂ : Type := g₂.nt,
  let N : Type := option (N₁ ⊕ N₂),

  let convert_sTN₁_sTN : (symbol T N₁) → (symbol T N) :=
    λ s, match s with
      | symbol.terminal st := (symbol.terminal st)
      | symbol.nonterminal snt := (symbol.nonterminal (some (sum.inl snt)))
    end,
  let convert_sTN₂_sTN : (symbol T N₂) → (symbol T N) :=
    λ s, match s with
      | symbol.terminal st := (symbol.terminal st)
      | symbol.nonterminal snt := (symbol.nonterminal (some (sum.inr snt)))
    end,

  have convert_sTN₁_sTN_nn : ∀ x, (convert_sTN₁_sTN x) ≠ (symbol.nonterminal none),
  {
    intro x,
    cases x,
    {
      change (symbol.terminal x) ≠ symbol.nonterminal none,
      finish,
    },
    {
      change (symbol.nonterminal (some (sum.inl x))) ≠ symbol.nonterminal none,
      finish,
    },
  },
  have convert_sTN₁_sTN_nns : ∀ xs, symbol.nonterminal none ∉ list.map convert_sTN₁_sTN xs,
  {
    finish,
  },
  have convert_sTN₂_sTN_nn : ∀ x, (convert_sTN₂_sTN x) ≠ (symbol.nonterminal none),
  {
    intro x,
    cases x,
    {
      change (symbol.terminal x) ≠ symbol.nonterminal none,
      finish,
    },
    {
      change (symbol.nonterminal (some (sum.inr x))) ≠ symbol.nonterminal none,
      finish,
    },
  },
  have convert_sTN₂_sTN_nns : ∀ xs, symbol.nonterminal none ∉ list.map convert_sTN₂_sTN xs,
  {
    finish,
  },

  let convert_lsTN₁_lsTN : list (symbol T N₁) → list (symbol T N) :=
    list.map convert_sTN₁_sTN,
  let convert_lsTN₂_lsTN : list (symbol T N₂) → list (symbol T N) :=
    list.map convert_sTN₂_sTN,

  let convert_rule₁_rule : (N₁ × (list (symbol T N₁))) → (N × (list (symbol T N))) :=
    λ r, (some (sum.inl (prod.fst r)), convert_lsTN₁_lsTN (prod.snd r)),
  let convert_rule₂_rule : (N₂ × (list (symbol T N₂))) → (N × (list (symbol T N))) :=
    λ r, (some (sum.inr (prod.fst r)), convert_lsTN₂_lsTN (prod.snd r)),
  
  let rules₁ : list (N × (list (symbol T N))) :=
    list.map convert_rule₁_rule g₁.rules,
  let rules₂ : list (N × (list (symbol T N))) :=
    list.map convert_rule₂_rule g₂.rules,

  let g := CF_grammar.mk N none (
    (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
    (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
    (rules₁ ++ rules₂)
  ),
  use g,
  
  apply set.eq_of_subset_of_subset,
  {
    let convert_sTN_sTN₂ : (symbol T N) → option (symbol T N₂) :=
      λ s, match s with
        | symbol.terminal st := some (symbol.terminal st)
        | symbol.nonterminal none := none
        | symbol.nonterminal (some (sum.inl _)) := none
        | symbol.nonterminal (some (sum.inr nt)) := some (symbol.nonterminal nt)
      end,

    set! convert_lsTN_lsTN₂ : list (symbol T N) → list (symbol T N₂) :=
      list.filter_map convert_sTN_sTN₂
    with convert_lsTN_lsTN₂',

    let convert_rule_rule₂ : (N × (list (symbol T N))) → option (N₂ × (list (symbol T N₂))) :=
      λ r, match r with
        | (none, _) := none
        | ((some (sum.inl _)), _) := none
        | ((some (sum.inr nt)), lis) := some (nt, convert_lsTN_lsTN₂ lis)
      end,

    -- prove `CF_language g ⊆ L₁ + L₂`
    intros w h,
    simp,
    unfold CF_language at h,
    change CF_generates_str g (list.map symbol.terminal w) at h,
    unfold CF_generates_str at h,
    unfold CF_derives at h,
    cases unpack_transitive_closure h sorry with ini foo,
    cases foo with deri_head deri_tail,
    cases deri_head with rule hhead,
    cases hhead with ruleok h',
    cases ruleok with g₁S bar,
    {
      left,
      sorry,
    },
    cases bar with g₂S imposs,
    {
      right,
      rw g₂S at h',
      simp at h',
      cases h' with u baz,
      cases baz with v conju,
      cases conju with bef aft,
      have len := congr_arg list.length bef,
      rw list.length_append u (symbol.nonterminal none :: v) at len,
      simp at len,
      have u_nil : u = [],
      {
        by_contradiction,
        rw ← list.length_eq_zero at h,
        have ul : u.length ≥ 1 :=
          nat.one_le_iff_ne_zero.mpr h,
        linarith,
      },
      have v_nil : v = [],
      {
        by_contradiction,
        rw ← list.length_eq_zero at h,
        have vl : v.length ≥ 1 :=
          nat.one_le_iff_ne_zero.mpr h,
        linarith,
      },
      rw u_nil at aft,
      rw v_nil at aft,
      rw list.nil_append at aft,
      have deri_indu : ∀ input output : list (symbol T N),
        (symbol.nonterminal none) ∉ input →
          CF_derives g input output →
            (symbol.nonterminal none) ∉ output ∧
            CF_derives g₂ (convert_lsTN_lsTN₂ input) (convert_lsTN_lsTN₂ output),
      {
        intros inp outp nni hyp,

        induction hyp with i_intermediate i_output i_what orig_prop ih,
        {
          split,
          {
            exact nni,
          },
          apply CF_derives_reflexive,
        },
        cases ih with no_none i_hy,

        rw convert_lsTN_lsTN₂',
        cases orig_prop with orig_rule orig_rest,
        cases orig_rest with orig_in orig_prop, -- name reused !
        cases orig_prop with orig_u orig_rest, -- name reused !
        cases orig_rest with orig_v orig_prop, -- name reused !
        cases orig_prop with orig_before orig_after,

        split,
        {
          rw orig_before at no_none,
          simp only [list.mem_append] at no_none,
          push_neg at no_none,
          have nn_orig_u : symbol.nonterminal none ∉ orig_u,
          {
            tauto,
          },
          have nn_orig_v : symbol.nonterminal none ∉ orig_v,
          {
            tauto,
          },
          have nn_orig_s : symbol.nonterminal none ∉ orig_rule.snd,
          {
            cases orig_in,
            {
              rw orig_in,
              simp,
            },
            cases orig_in,
            {
              rw orig_in,
              simp,
            },
            change orig_rule ∈ (rules₁ ++ rules₂) at orig_in,
            rw list.mem_append at orig_in,
            cases orig_in,
            {
              change orig_rule ∈ list.map convert_rule₁_rule g₁.rules at orig_in,
              change orig_rule ∈ list.map (λ (r : N₁ × list (symbol T N₁)), (some (sum.inl r.fst), convert_lsTN₁_lsTN r.snd)) g₁.rules at orig_in,
              change orig_rule ∈ list.map (λ (r : N₁ × list (symbol T N₁)), (some (sum.inl r.fst), (list.map convert_sTN₁_sTN) r.snd)) g₁.rules at orig_in,
              have uuuuu : orig_rule.snd ∈ list.map prod.snd (list.map (λ (r : N₁ × list (symbol T N₁)), (some (sum.inl r.fst), list.map convert_sTN₁_sTN r.snd)) g₁.rules),
              {
                exact list.mem_map_of_mem prod.snd orig_in,
              },
              {
                simp at uuuuu,
                cases uuuuu with uuuuu_a uuuuu_u,
                cases uuuuu_u with uuuuu_b uuuuu_r,
                cases uuuuu_r with uuuuu_ uuu,
                rw ← uuu,
                exact convert_sTN₁_sTN_nns uuuuu_b,
              },
            },
            {
              change orig_rule ∈ list.map convert_rule₂_rule g₂.rules at orig_in,
              change orig_rule ∈ list.map (λ (r : N₂ × list (symbol T N₂)), (some (sum.inr r.fst), convert_lsTN₂_lsTN r.snd)) g₂.rules at orig_in,
              change orig_rule ∈ list.map (λ (r : N₂ × list (symbol T N₂)), (some (sum.inr r.fst), (list.map convert_sTN₂_sTN) r.snd)) g₂.rules at orig_in,
              have uuuuu : orig_rule.snd ∈ list.map prod.snd (list.map (λ (r : N₂ × list (symbol T N₂)), (some (sum.inr r.fst), list.map convert_sTN₂_sTN r.snd)) g₂.rules),
              {
                exact list.mem_map_of_mem prod.snd orig_in,
              },
              {
                simp at uuuuu,
                cases uuuuu with uuuuu_a uuuuu_u,
                cases uuuuu_u with uuuuu_b uuuuu_r,
                cases uuuuu_r with uuuuu_ uuu,
                rw ← uuu,
                exact convert_sTN₂_sTN_nns uuuuu_b,
              },
            },
          },
          rw orig_after,
          intro ass_in_orig,
          simp only [list.mem_append] at ass_in_orig,
          tauto,
        },

        fconstructor,
          exact convert_lsTN_lsTN₂ i_intermediate,
        {
          apply i_hy,
        },

        have no_none_middle : (symbol.nonterminal none) ∉ [symbol.nonterminal orig_rule.fst],
        {
          intro fals,
          have falss : (symbol.nonterminal none) ∈ (orig_u ++ [symbol.nonterminal orig_rule.fst] ++ orig_v),
          {
            simp only [list.mem_append],
            left,
            right,
            exact fals,
          },
          rw ← orig_before at falss,
          exact no_none falss,
        },
        have not_none : (symbol.nonterminal orig_rule.fst) ≠ (symbol.nonterminal none),
        {
          intro cont,
          rw list.mem_cons_eq at no_none_middle,
          apply no_none_middle,
          left,
          exact eq.symm cont,
        },

        have orig_rule_place: orig_rule ∈ rules₂,
        {
          cases orig_in,
          {
            finish,
          },
          cases orig_in,
          {
            finish,
          },
          change orig_rule ∈ (rules₁ ++ rules₂) at orig_in,
          rw list.mem_append at orig_in,
          cases orig_in,
          {
            exfalso,

            sorry,
          },
          exact orig_in,
        },

        unfold CF_transforms,
        let converted_rule := convert_rule_rule₂ orig_rule,
        have not_lost : ∃ converted_rule_val, converted_rule = some converted_rule_val,
        {
          change orig_rule ∈ list.map convert_rule₂_rule g₂.rules at orig_rule_place,
          have aaaaa : ∃ preconve_rule ∈ g₂.rules, convert_rule₂_rule preconve_rule = orig_rule,
          {
            
            sorry,
          },

          sorry,
        },
        cases not_lost with converted_rule_val converted_rule_some,
        use converted_rule_val,
        split,
        {
          
          sorry,
        },
        use list.filter_map convert_sTN_sTN₂ orig_u,
        use list.filter_map convert_sTN_sTN₂ orig_v,
        have converted_before := congr_arg (list.filter_map convert_sTN_sTN₂) orig_before,
        have converted_after := congr_arg (list.filter_map convert_sTN_sTN₂) orig_after,
        rw list.filter_map_append at converted_before,
        rw list.filter_map_append at converted_before,
        rw list.filter_map_append at converted_after,
        rw list.filter_map_append at converted_after,

        have conversion_id_before : 
          list.filter_map convert_sTN_sTN₂ [symbol.nonterminal orig_rule.fst] = [symbol.nonterminal converted_rule_val.fst],
        {
          sorry,
        },
        have conversion_id_after : 
          list.filter_map convert_sTN_sTN₂ orig_rule.snd = converted_rule_val.snd,
        {
          sorry,
        },
        rw conversion_id_before at converted_before,
        rw conversion_id_after at converted_after,
        tauto,
      },

      have start_word : [symbol.nonterminal g₂.initial] = (convert_lsTN_lsTN₂ ini),
      {
        rw aft,
        refl,
      },
      have final_word : (list.map symbol.terminal w) = (convert_lsTN_lsTN₂ (list.map symbol.terminal w)),
      {
        rw convert_lsTN_lsTN₂',
        
        sorry,
      },

      rw ← h₂,
      change CF_generates_str g₂ (list.map symbol.terminal w),
      unfold CF_generates_str,
      unfold CF_derives,
      rw start_word,
      rw final_word,
      cases deri_indu ini (list.map symbol.terminal w) sorry deri_tail with irrelevant relevant,
      exact relevant,
    },
    exfalso,

    cases h' with u baz,
    cases baz with v conju,
    cases conju with bef aft,
    have len := congr_arg list.length bef,
    rw list.length_append at len,
    simp at len,
    have u_nil : u = [],
    {
      by_contradiction,
      rw ← list.length_eq_zero at h,
      have ul : u.length ≥ 1 :=
        nat.one_le_iff_ne_zero.mpr h,
      linarith,
    },
    have v_nil : v = [],
    {
      by_contradiction,
      rw ← list.length_eq_zero at h,
      have vl : v.length ≥ 1 :=
        nat.one_le_iff_ne_zero.mpr h,
      linarith,
    },
    rw u_nil at bef,
    rw v_nil at bef,
    rw list.nil_append at bef,
    rw list.append_nil at bef,
    change [symbol.nonterminal none] = [symbol.nonterminal rule.fst] at bef,
    have rule_root : rule.fst = none,
    {
      finish,
    },
    change rule ∈ (rules₁ ++ rules₂) at imposs,
    rw list.mem_append at imposs,
    cases imposs;
    finish,
  },

  -- prove `L₁ + L₂ ⊆ CF_language g`
  intros w h,
  rw language.mem_add at h,
  cases h with case₁ case₂,
  {
    have deri_start : CF_derives g [symbol.nonterminal none] [symbol.nonterminal (some (sum.inl g₁.initial))],
    {
      fconstructor,
        exact [symbol.nonterminal none],
      refl,
      use (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]),
      split,
        finish,
      use [[], []],
      simp,
    },

    have deri_rest : CF_derives g [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w),
    {
      have deri_orig : CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal w),
      {
        finish,
      },
      dsimp at *,
      have deri_step : ∀ input output : list (symbol T N₁),
                        CF_transforms g₁ input output →
                        CF_transforms g (convert_lsTN₁_lsTN input) (convert_lsTN₁_lsTN output),
      {
        intros inpu outpu ass,
        cases ass with rul foo,
        cases foo with bel bar,
        cases bar with v baz,
        cases baz with w hyp,
        cases hyp with befo afte,

        use convert_rule₁_rule rul,
        split,
        {
          change convert_rule₁_rule rul ∈ (
            (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
            (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
            (list.map convert_rule₁_rule g₁.rules) ++ rules₂),
          have isthere : convert_rule₁_rule rul ∈ list.map convert_rule₁_rule g₁.rules :=
            list.mem_map_of_mem convert_rule₁_rule bel,
          finish,
        },
        use convert_lsTN₁_lsTN v,
        use convert_lsTN₁_lsTN w,
        split,
        {
          rw congr_arg convert_lsTN₁_lsTN befo,
          apply list_three_parts,
        },
        {
          change convert_lsTN₁_lsTN outpu = convert_lsTN₁_lsTN v ++ convert_lsTN₁_lsTN rul.snd ++ convert_lsTN₁_lsTN w,
          rw congr_arg convert_lsTN₁_lsTN afte,
          apply list_three_parts,
        },
      },
      have deri_more : ∀ input output : list (symbol T N₁),
                         CF_derives g₁ input output →
                         CF_derives g (convert_lsTN₁_lsTN input) (convert_lsTN₁_lsTN output),
      {
        intros inp outp ass,
        induction ass with u v ih₁ orig ih,
        {
          apply CF_derives_reflexive,
        },
        apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
          finish,
        fconstructor,
          exact (convert_lsTN₁_lsTN u),
        refl,
        exact deri_step u v orig,
      },
      have beginning : [symbol.nonterminal (some (sum.inl g₁.initial))]
                       = convert_lsTN₁_lsTN [symbol.nonterminal g₁.initial],
      {
        finish,
      },
      have ending : (list.map symbol.terminal w)
                    = convert_lsTN₁_lsTN (list.map symbol.terminal w),
      {
        ext1,
        simp,
      },
      rw beginning,
      rw ending,
      exact deri_more [symbol.nonterminal g₁.initial] (list.map symbol.terminal w) deri_orig,
    },

    unfold CF_language,
    change CF_generates_str g (list.map symbol.terminal w),
    unfold CF_generates_str,
    unfold CF_derives,
    apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
      finish, -- uses `deri_start` here
    exact deri_rest,
  },

  {
    have deri_start : CF_derives g [symbol.nonterminal none] [symbol.nonterminal (some (sum.inr g₂.initial))],
    {
      fconstructor,
        exact [symbol.nonterminal none],
      refl,
      use (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]),
      split,
        finish,
      use [[], []],
      simp,
    },

    have deri_rest : CF_derives g [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w),
    {
      have deri_orig : CF_derives g₂ [symbol.nonterminal g₂.initial] (list.map symbol.terminal w),
      {
        finish,
      },
      dsimp at *,
      have deri_step : ∀ input output : list (symbol T N₂),
                        CF_transforms g₂ input output →
                        CF_transforms g (convert_lsTN₂_lsTN input) (convert_lsTN₂_lsTN output),
      {
        intros inpu outpu ass,
        cases ass with rul foo,
        cases foo with bel bar,
        cases bar with v baz,
        cases baz with w hyp,
        cases hyp with befo afte,

        use convert_rule₂_rule rul,
        split,
        {
          change convert_rule₂_rule rul ∈ (
            (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
            (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
            rules₁ ++ (list.map convert_rule₂_rule g₂.rules)),
          have isthere : convert_rule₂_rule rul ∈ list.map convert_rule₂_rule g₂.rules :=
            list.mem_map_of_mem convert_rule₂_rule bel,
          finish,
        },
        use convert_lsTN₂_lsTN v,
        use convert_lsTN₂_lsTN w,
        split,
        {
          rw congr_arg convert_lsTN₂_lsTN befo,
          apply list_three_parts,
        },
        {
          change convert_lsTN₂_lsTN outpu = convert_lsTN₂_lsTN v ++ convert_lsTN₂_lsTN rul.snd ++ convert_lsTN₂_lsTN w,
          rw congr_arg convert_lsTN₂_lsTN afte,
          apply list_three_parts,
        },
      },
      have deri_more : ∀ input output : list (symbol T N₂),
                         CF_derives g₂ input output →
                         CF_derives g (convert_lsTN₂_lsTN input) (convert_lsTN₂_lsTN output),
      {
        intros inp outp ass,
        induction ass with u v ih₂ orig ih,
        {
          apply CF_derives_reflexive,
        },
        apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
          finish,
        fconstructor,
          exact (convert_lsTN₂_lsTN u),
        refl,
        exact deri_step u v orig,
      },
      have beginning : [symbol.nonterminal (some (sum.inr g₂.initial))]
                       = convert_lsTN₂_lsTN [symbol.nonterminal g₂.initial],
      {
        finish,
      },
      have ending : (list.map symbol.terminal w)
                    = convert_lsTN₂_lsTN (list.map symbol.terminal w),
      {
        ext1,
        simp,
      },
      rw beginning,
      rw ending,
      exact deri_more [symbol.nonterminal g₂.initial] (list.map symbol.terminal w) deri_orig,
    },

    unfold CF_language,
    change CF_generates_str g (list.map symbol.terminal w),
    unfold CF_generates_str,
    unfold CF_derives,
    apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
      finish, -- uses `deri_start` here
    exact deri_rest,
  },
end


theorem CF_intersection_Reg {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
  is_CF L₁ ∧ is_Reg L₂ → is_CF (set.inter L₁ L₂) :=
sorry


theorem CF_under_concatenation {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
  is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ * L₂) :=
sorry
