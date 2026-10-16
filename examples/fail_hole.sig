-- Must FAIL, each independently.
-- Undetermined holes are errors (with locations and expected types), never
-- guesses and never silence: nothing here constrains the `_`.
def bad : (A:*) -> A -> A = \A x. _;
-- Holes in infer position have no expected type to synthesize from.
def bad2 : Unit = _ ();
-- A `_` annotation cannot save a value that never infers on its own.
def bad3 : _ = \x. x;
