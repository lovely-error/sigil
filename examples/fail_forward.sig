-- Must FAIL: forward reference (`a` mentions `b` before it is defined).
def a : Type0 = b;
def b : Type0 = *;
