require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred;

symbol b : τ ι;

symbol f : τ (ι ⤳ ι);
symbol g : τ (ι ⤳ ι);
symbol h : τ (ι ⤳ ι ⤳ ι);
symbol w : τ (ι ⤳ ι ⤳ ι);

symbol q : τ (ι ⤳ ι ⤳ o);

symbol eq_point x : π (f x = g x);

symbol target_one_binder :
  π ((∀ (λ x, q (g x) b)) = ⊤);

symbol test_rewrite_under_one_binder :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite eq_point;
  refine target_one_binder
end;

symbol eq_redex x :
  π (w (f x) (g x) = g x);

symbol target_redex_function :
  π ((∀ (λ x, q (g x) b)) = ⊤);

symbol test_rewrite_under_redex_function :
  π ((∀ (λ x, q (w (f x) (g x)) b)) = ⊤) ≔
begin
  rewrite eq_redex;
  refine target_redex_function
end;

symbol target_preserve_context :
  π ((∀ (λ x, q (g x) x)) = ⊤);

symbol test_rewrite_under_binder_preserve_context :
  π ((∀ (λ x, q (w (f x) (g x)) x)) = ⊤) ≔
begin
  rewrite eq_redex;
  refine target_preserve_context
end;

symbol eq_two_binders x y :
  π (w (f x) (g y) = h x y);

symbol target_two_binders :
  π ((∀ (λ x, ∀ (λ y, q (h x y) b))) = ⊤);

symbol test_rewrite_under_two_binders :
  π ((∀ (λ x, ∀ (λ y, q (w (f x) (g y)) b))) = ⊤) ≔
begin
  rewrite eq_two_binders;
  refine target_two_binders
end;

symbol target_inner_binder_only :
  π ((∀ (λ x, ∀ (λ y, q x (g y)))) = ⊤);

symbol test_rewrite_under_inner_binder_only :
  π ((∀ (λ x, ∀ (λ y, q x (f y)))) = ⊤) ≔
begin
  rewrite eq_point;
  refine target_inner_binder_only
end;
