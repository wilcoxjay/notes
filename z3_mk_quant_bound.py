def z3_mk_quantifier_bound(is_forall, names, sorts, body, weight=1, qid="", skid="", patterns=[], no_patterns=[]): # type: ignore
    ctx = body.ctx
    if isinstance(names, str):
        names = [names]
    num_names = len(names)
    if num_names == 0:
        return body
    _names = (z3.Symbol * num_names)()
    for i in range(num_names):
        _names[i] = z3.to_symbol(names[i], ctx)
    if z3.is_sort(sorts):
        sorts = [sorts]
    num_sorts = len(sorts)
    if num_sorts != num_names:
        raise Exception
    if num_sorts == 0:
        return body
    _sorts = (z3.Sort * num_sorts)()
    for i in range(num_sorts):
        _sorts[i] = sorts[i].ast
    patterns = [ z3._to_pattern(p) for p in patterns ]
    num_pats = len(patterns)
    _pats = (z3.Pattern * num_pats)()
    for i in range(num_pats):
        _pats[i] = patterns[i].ast

    num_no_pats = len(no_patterns)
    _no_pats = (z3.Ast * num_no_pats)()
    for i in range(num_no_pats):
        _no_pats[i] = no_patterns[i].as_ast()

    qid  = z3.to_symbol(qid, ctx)
    skid = z3.to_symbol(skid, ctx)
    return z3.QuantifierRef(z3.Z3_mk_quantifier_ex(ctx.ref(), is_forall, weight, qid, skid,
                                                   num_pats, _pats,
                                                   num_no_pats, _no_pats,
                                                   num_sorts, _sorts,
                                                   _names,
                                                   body.as_ast()), ctx)
