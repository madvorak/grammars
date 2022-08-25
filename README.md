# Formalization of formal grammars

I formalize formal grammars in Lean. I started with context-free grammars. Hopefully, this project will cover the whole Chomsky hierarchy in the future.

## Highlights of what has been done so far

[Main definition](https://github.com/madvorak/grammars/blob/59735364bf134829f31cb74465644f80095371ed/src/context_free/cfg.lean#L7) of a context-free grammar.

[Example proof](https://github.com/madvorak/grammars/blob/59735364bf134829f31cb74465644f80095371ed/test/cfg_demo.lean#L28) that a concrete word belongs to a language of a concrete grammar.

[Precise characterisation](https://github.com/madvorak/grammars/blob/59735364bf134829f31cb74465644f80095371ed/test/cfg_demo.lean#L105) of a language generated by that grammar.

[General grammars](https://github.com/madvorak/grammars/blob/59735364bf134829f31cb74465644f80095371ed/src/unrestricted/grammar.lean#L20) were defined.

### Finished proofs about context-free closure properties

The class of context-free languages is closed under [reversal](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/reverse_CF.lean).

The class of context-free languages is closed under [union](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_union_CF.lean).

The class of context-free languages is not closed under [intersection](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_intersection_CF.lean).

The class of context-free languages is not closed under [complement](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/complement_CF.lean).

The class of context-free languages is closed under [concatenation](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_concatenation_CF.lean).

### Finished proofs about recursively-enumerable closure properties

The class of recursively-enumerable languages is closed under [reversal](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/unary/reverse_RE.lean).

The class of recursively-enumerable languages is closed under [union](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_union_RE.lean).

The class of recursively-enumerable languages is closed under [concatenation](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_concatenation_RE.lean).
