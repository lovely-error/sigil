-- Must FAIL, each independently: Void has no introduction ...
def bad : Void = \x. x;
def bad2 : Void = *;
-- ... and `absurd`'s arguments are still validated (scrutinee `*` fits
-- nowhere near `Void`, even though elimination is vacuous).
def bad3 : * = absurd * *;
