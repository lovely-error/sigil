-- Must FAIL: quantifying over `Type0` lands in `Type1`, never `Type0`
-- (predicative Pi above `*`: the domain's sort feeds the max).
def bad : Type0 = (A : Type0) -> A -> A;
