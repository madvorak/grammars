import classes.context_free.toolbox
import classes.unrestricted.toolbox


variables {T : Type}

def grammar_of_cfg (g : CF_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map (λ r : g.nt × (list (symbol T g.nt)),
  grule.mk [] r.fst [] r.snd) g.rules)

lemma CF_language_eq_grammar_language (g : CF_grammar T) :
  CF_language g = grammar_language (grammar_of_cfg g) :=
begin
  unfold CF_language grammar_language,
  ext,
  rw [set.mem_set_of_eq, set.mem_set_of_eq],
  unfold CF_generates grammar_generates,
  split;
  intro ass,
  {
    induction ass with x y trash hyp ih,
    {
      apply grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran ih,
    rcases hyp with ⟨r, rin, u, v, bef, aft⟩,
    use grule.mk [] r.fst [] r.snd,
    split,
    {
      delta grammar_of_cfg,
      dsimp only,
      rw list.mem_map,
      exact ⟨r, rin, rfl⟩,
    },
    use [u, v],
    split,
    {
      simp only [list.append_nil],
      exact bef,
    },
    {
      exact aft,
    },
  },
  {
    induction ass with x y trash hyp ih,
    {
      apply CF_deri_self,
    },
    apply CF_deri_of_deri_tran ih,
    rcases hyp with ⟨r, rin, u, v, bef, aft⟩,
    delta grammar_of_cfg at rin,
    rw list.mem_map at rin,
    rcases rin with ⟨r₀, rin₀, eq_r⟩,
    use r₀,
    split,
    {
      exact rin₀,
    },
    use [u, v],
    split,
    {
      rw ←eq_r at bef,
      simpa only [list.append_nil] using bef,
    },
    {
      rw ←eq_r at aft,
      exact aft,
    },
  },
end

theorem CF_subclass_T0 {L : language T} :
  is_CF L → is_T0 L :=
begin
  rintro ⟨g, eq_L⟩,
  use grammar_of_cfg g,
  rw ←eq_L,
  rw CF_language_eq_grammar_language,
end
