-- Must FAIL, each independently.
-- Too many arguments: the second application hits `Type0`, not a function.
def bad : Type0 = ((\x. x) : * -> Type0) * *;
-- Applying a sort (`*` lives in `Type0`, never applies).
def bad2 : * = * *;
