require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred;

symbol b : τ ι;

symbol f : τ (ι ⤳ ι);
symbol g : τ (ι ⤳ ι);
symbol h : τ (ι ⤳ ι ⤳ ι);
symbol w : τ (ι ⤳ ι ⤳ ι);

symbol q : τ (ι ⤳ ι ⤳ o);

symbol eq_point x : π (f x = g x);

symbol eq_lambda : π ((λ x, f x) = (λ x, g x)) ≔
  funExt (λ x, f x) (λ x, g x) eq_point;

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

symbol test_rewrite_named_binder_pattern :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[in (λ y, q (f y) b)] eq_point;
  refine target_one_binder
end;

symbol test_rewrite_binder_redex_pattern :
  π ((∀ (λ x, q ((λ y, f y) x) b)) = ⊤) ≔
begin
  rewrite .[(λ z, f z)] eq_lambda;
  refine target_one_binder
end;

symbol target_dependent_wildcard :
  π ((∀ (λ x, q (g x) x)) = ⊤);

symbol test_rewrite_dependent_wildcard :
  π ((∀ (λ x, q (f x) x)) = ⊤) ≔
begin
  rewrite .[in (λ y, q (f y) _)] eq_point;
  refine target_dependent_wildcard
end;

symbol test_rewrite_anonymous_binder_pattern :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[in (λ _, q (f _) b)] eq_point;
  refine target_one_binder
end;

symbol test_rewrite_contextual_binder_pattern :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol test_rewrite_contextual_binder_region :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[in y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol test_rewrite_contextual_binder_explicit :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[f _ in y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol target_contextual_region :
  π ((∀ (λ x, q (w (g x) (g x)) b)) = ⊤);

symbol test_rewrite_contextual_binder_region_nested :
  π ((∀ (λ x, q (w (f x) (g x)) b)) = ⊤) ≔
begin
  rewrite .[in y in (λ x, q y b)] eq_point;
  refine target_contextual_region
end;

symbol test_rewrite_contextual_binder_explicit_nested :
  π ((∀ (λ x, q (w (f x) (g x)) b)) = ⊤) ≔
begin
  rewrite .[f _ in y in (λ x, q y b)] eq_point;
  refine target_contextual_region
end;

symbol test_rewrite_contextual_binder_as :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[f _ as y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol target_repeated_context :
  π ((∀ (λ x, q (g x) (g x))) = ⊤);

symbol test_rewrite_repeated_context :
  π ((∀ (λ x, q (f x) (f x))) = ⊤) ≔
begin
  rewrite .[y in (λ x, q y y)] eq_point;
  refine target_repeated_context
end;

symbol test_rewrite_contextual_two_binders :
  π ((∀ (λ x, ∀ (λ y, q (w (f x) (g y)) b))) = ⊤) ≔
begin
  rewrite .[z in (λ x, ∀ (λ y, q z b))] eq_two_binders;
  refine target_two_binders
end;

symbol target_let_pattern : π ((q (g b) b) = ⊤);

symbol test_rewrite_let_pattern :
  π ((let y : τ ι ≔ f b in q y b) = ⊤) ≔
begin
  rewrite .[in (let y : τ ι ≔ f b in q y b)] eq_point;
  refine target_let_pattern
end;
