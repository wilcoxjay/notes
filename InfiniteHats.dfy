type Player

datatype Color = Red | Blue

function AxiomOfChoice<A>(F: iset<iset<A>>): (chooser: imap<iset<A>, A>)
    requires iset{} !in F
    ensures forall S | S in F :: S in chooser && chooser[S] in S

function Strategy(p: Player, assignment: imap<Player, Color>): (color: Color)
    requires forall p' | p != p' :: p' in assignment

lemma Hats(assignment: imap<Player, Color>)
    requires forall p: Player :: p in assignment
{
    var guesses: imap<Player, Color>;
    assume forall p ::
        var others := imap p' | p != p' :: assignment[p'];
        p in guesses &&
        guesses[p] == Strategy(p, others);

}

