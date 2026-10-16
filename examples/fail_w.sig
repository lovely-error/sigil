-- Must FAIL, each independently.
-- Scrutinee must be a W-tree (`v : Void` is not one).
def bad : (v:Void) -> Void = \v. w_rect Void (\_. Void) (\_. Void) (\a f ih. absurd Void a) v;
-- Branch must inhabit the motive at the pattern (here `*`, which
-- `absurd Void a : Void` is not — though the large motive itself is legal).
def bad2 : (v:Void) -> Void = \v. w_rect Void (\_. Void) (\_. *) (\a f ih. absurd Void a) (sup Void (\_. Void) v (\x. absurd (W Void (\_. Void)) x));
-- `W` over a universe lives above `*` (`*` as labels lifts out of `*`).
def bad3 : * = W * (\_. *);
