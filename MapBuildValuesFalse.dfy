// RUN: /nologo /print:tmp.bpl /compile:0

lemma MapValues()
    ensures false
{
    var m := map[0 := false];
    var m' := m[0 := true];

    assert m'.Values == m.Values + {true};
    assert false;
}

lemma IMapValues()
    ensures false
{
    var m := imap[0 := false];
    var m' := m[0 := true];

    assert m'.Values == m.Values + iset{true};
    assert false;
}
