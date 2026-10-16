-- Must FAIL: self reference (no recursion in the core).
def loop : Type0 = loop;
