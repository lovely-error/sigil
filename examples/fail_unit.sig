-- Must FAIL, each independently.
-- `()` fits `Unit` only (not `Void`) ...
def bad : Void = ();
-- ... and `Unit` the type is not a term of itself.
def bad2 : Unit = Unit;
-- Branch must fit the motive (`()` is not a `Void`).
def bad3 : (u:Unit) -> Void = \u. unit_rect (\_. Void) () u;
