-- Must FAIL, each independently.
-- Ascriptions are checked, not stripped: `(() : Void)` claims `()` at a
-- type it does not inhabit, and `(Void : Unit)` claims `Void` in a
-- universe it does not live in.
def bad : Unit = (() : Void);
def bad2 : * = (Void : Unit);
