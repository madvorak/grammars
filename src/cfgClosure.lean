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

    let convert_lsTN_lsTN₂ : list (symbol T N) → list (symbol T N₂) :=
      list.filter_map convert_sTN_sTN₂,
/-
    let convert_rule_rule₂ : (N × (list (symbol T N))) → (N₂ × (list (symbol T N₂))) :=
      λ r, (symbol.nonterminal (prod.fst r)), convert_lsTN_lsTN₂ (prod.snd r)),
-/
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
                         CF_derives g input output →
                         CF_derives g₂ (convert_lsTN_lsTN₂ input) (convert_lsTN_lsTN₂ output),
      {
        intros inp outp hyp,
        induction hyp with u v ih₂ orig ih,
        {
          apply CF_derives_reflexive,
        },
        apply @trans _ (CF_derives g₂) (is_trans.mk relation.transitive_refl_trans_gen),
        {
          exact ih,
        },
        fconstructor,
          exact (convert_lsTN_lsTN₂ u),
        refl,

        cases orig with orig_rule orig_rest,
        cases orig_rest with orig_in orig_prop,
        cases orig_prop with prefi foo,
        cases foo with postfi orig_two,
        cases orig_two with orig_pre orig_post,

        -- TODO continue here
        sorry,
      },
      have start_word : [symbol.nonterminal g₂.initial] = (convert_lsTN_lsTN₂ ini),
      {
        rw aft,
        refl,
      },
      have final_word : (list.map symbol.terminal w) = (convert_lsTN_lsTN₂ (list.map symbol.terminal w)),
      {
        
        sorry,
      },

      rw ← h₂,
      change CF_generates_str g₂ (list.map symbol.terminal w),
      unfold CF_generates_str,
      unfold CF_derives,
      rw start_word,
      rw final_word,
      exact deri_indu ini (list.map symbol.terminal w) deri_tail,
    },
    exfalso,

    sorry,
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
