function Ack(m: nat, n: nat): nat
{
    if m == 0 then
        n + 1
    else if n == 0 then
        Ack(m - 1, 1)
    else
        Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} Ack_Gt0(m: nat, n: nat)
    ensures Ack(m, n) > 0
{
    if m == 0 {
    } else if n == 0 {
        Ack_Gt0(m - 1, 1);
    } else {
        Ack_Gt0(m - 1, Ack(m, n - 1));
    }
}
