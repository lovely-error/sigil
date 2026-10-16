-- Must FAIL as stated: Hurkens' V needs `A -> *` at small level to close in
-- `*`; here that arrow lives in `Type0`, so V lands in `Type0`. The paradox's
-- self-membership switch (`V : *`) is rejected by stratification.
-- (Uncomment the second line to see V check at `Type0`.)
def v : * = (A:*) -> ((A -> *) -> (A -> *)) -> A -> *;
