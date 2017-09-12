type Msg;
const unique M1: Msg;
const unique M2: Msg;
const unique M3: Msg;
const unique M4: Msg;

function CaseSplit(m: Msg): bool { true }

axiom (forall m: Msg :: {CaseSplit(m)} m == M1 || m == M2 || m == M3 || m == M4);

const tMsg: Msg;
procedure Test()
{
	var tMsg1: Msg;
	havoc tMsg1;
    assert CaseSplit(tMsg1) && (tMsg1 == M1 || tMsg1 == M2  || tMsg1 == M3 || tMsg1 == M4);
    assert CaseSplit(tMsg) && (tMsg == M1 || tMsg == M2  || tMsg == M3 || tMsg == M4);
}


function IsM1(m: Msg): bool { m == M1 }
function IsM2(m: Msg): bool { m == M1 }
function IsM3(m: Msg): bool { m == M1 }
function IsM4(m: Msg): bool { m == M1 }

axiom (forall m: Msg :: IsM1(m) || IsM2(m) || IsM3(m) || IsM4(m));

procedure Test2()
{
	var tMsg1: Msg;
	havoc tMsg1;
    assert IsM1(tMsg1) || IsM2(tMsg1) || IsM3(tMsg1) || IsM4(tMsg1);
    assert IsM1(tMsg) || IsM2(tMsg) || IsM3(tMsg) || IsM4(tMsg);
}
