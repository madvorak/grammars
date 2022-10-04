# Formalization of formal grammars

I formalize formal grammars in Lean. I started with context-free grammars. Hopefully, this project will cover the whole Chomsky hierarchy in the future.

### Context-free grammars

[Definition](https://github.com/madvorak/grammars/blob/main/src/context_free/cfg.lean)

[Example](https://github.com/madvorak/grammars/blob/main/test/cfg_demo.lean)

The class of context-free languages is closed under [union](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_union_CF.lean)

The class of context-free languages is not closed under [intersection](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_intersection_CF.lean)

The class of context-free languages is not closed under [complement](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/complement_CF.lean)

The class of context-free languages is closed under [concatenation](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/binary/CF_concatenation_CF.lean)

The class of context-free languages is closed under [reversal](https://github.com/madvorak/grammars/blob/main/src/context_free/closure_properties/unary/reverse_CF.lean)

### Recursively-enumerable grammars

[Definition](https://github.com/madvorak/grammars/blob/main/src/unrestricted/grammar.lean)

[Example](https://github.com/madvorak/grammars/blob/main/test/grammar_demo.lean)

The class of recursively-enumerable languages is closed under [union](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_union_RE.lean)

The class of recursively-enumerable languages is closed under [concatenation](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/binary/RE_concatenation_RE.lean)

The class of recursively-enumerable languages is closed under [reversal](https://github.com/madvorak/grammars/blob/main/src/unrestricted/closure_properties/unary/reverse_RE.lean)
