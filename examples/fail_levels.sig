-- Must FAIL, each independently: no universe contains itself
-- (`Type0 : Type1`, never `Type0 : Type0` — the stratified Girard-analog).
def bad : Type0 = Type0;
-- A `Type2`-type never fits in `Type1` (cumulativity only goes up).
def bad2 : Type1 = Type2 -> Type2;
