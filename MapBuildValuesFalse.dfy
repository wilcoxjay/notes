// RUN: /nologo /print:tmp.bpl /compile:0

lemma Test(m: map<int, bool>)
    requires m.Keys == {0}
    requires !m[0]
    ensures false
{
    assert m.Values == {false};
    
    var m' := m[0 := true]; 
    assert m'.Values == m.Values + {true};
    assert m'.Values == {true};
    assert {false} + {true} == {true};
    assert false;
}


method Main()
{
    var m := map[0 := false];
    Test(m);
    assert false;
}
