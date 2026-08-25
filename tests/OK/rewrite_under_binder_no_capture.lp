require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred tests.OK.PropExt tests.OK.Tactic;

builtin "arr" ≔ ⤳;
builtin "funExt" ≔ funExt;

symbol p : τ (ι ⤳ o);

opaque symbol test_rewrite_under_binder_no_capture :
  π ((∀ (λ x, ¬ ¬ p x)) ⇒ (∀ (λ x, p x))) ≔
begin
  rewrite ¬¬ₑ_eq;
  eval (#try (#rewrite "" "" [prop] ∀_const));
  simplify;
  assume h;
  refine h
end;
