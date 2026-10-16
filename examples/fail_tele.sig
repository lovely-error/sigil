-- Must FAIL, each independently.
-- Telescope defs (`def f (x:A) ...`): binder types scope in order (no forward
-- references), and codomain inference (`=`, no return type) needs a type for
-- a body — terms are rejected, exactly like bad annotations. Large aliases
-- still respect cumulativity (a `Type0` type is not a `*` type).
def bad (A : *) = ();
def bad2 (A : Nat) = A;
def bad3 (A : B) (B : *) = A;
def bigalias (A : Type) = A;
def bad4 : * = bigalias Type0;
