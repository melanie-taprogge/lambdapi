require open tests.OK.rewrite_under_binders;

symbol test_rewrite_binder_pattern_wrong_variable :
  π ((∀ (λ x, q (f b) b)) = ⊤) ≔
begin
  rewrite .[in (λ y, q (f y) b)] eq_point
end;
