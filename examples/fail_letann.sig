-- Must FAIL, each independently.
-- `let` bindings inside annotations are checked, not just unfolded: the
-- binding `X : Void = ()` is ill-typed wherever it appears.
def bad : (let X : Void = () in Unit) = ();
def bad2 : ((let X : Void = () in Unit) -> Unit) = \x. x;
