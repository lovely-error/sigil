-- Must FAIL, each independently.
-- Hole solutions are checked against the hole's recorded type: `?m : Type0`
-- cannot be solved by `Type0` itself (that would derive `Type0 : Type0`,
-- which `fail_levels.sig` forbids in explicit form).
def g : (A:Type0) -> A -> A = \A x. x;
def bad : Type0 = g _ *;
def f : (A:Type0) -> (x:A) -> Type0 = \A x. A;
def bad2 : Type0 = f _ *;
