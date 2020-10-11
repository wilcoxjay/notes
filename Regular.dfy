// inspired by https://stackoverflow.com/questions/64178349/how-to-define-this-regular-language-in-dafny
// this file shows that the L from that post is recognized by an NFA

predicate IsAOrB(c: char)
{
  c == 'a' || c == 'b'
}

predicate ContainsOnlyAsAndBs(s: string)
{
  forall c | c in s :: IsAOrB(c)
}

predicate InL(w: string)
  requires ContainsOnlyAsAndBs(w)
{
  exists x | ContainsOnlyAsAndBs(x) && x != [] :: w == ['a'] + x + ['a']
}

function L(): iset<string>
{
  iset s | ContainsOnlyAsAndBs(s) && InL(s)
}

datatype NFA<S> = NFA(
  alphabet: set<char>,
  states: set<S>,
  initial: set<S>,
  accepting: set<S>,
  epsilon_step: map<S, set<S>>,
  char_step: map<(S,char), set<S>>
)

predicate WFNFA<S>(nfa: NFA<S>)
{
  && nfa.initial <= nfa.states
  && nfa.accepting <= nfa.states
  && (forall s | s in nfa.states ::
        s in nfa.epsilon_step && nfa.epsilon_step[s] <= nfa.states)
  && (forall s, c | s in nfa.states && c in nfa.alphabet ::
       (s, c) in nfa.char_step && nfa.char_step[(s,c)] <= nfa.states)
}

function RelationStep<S>(universe: set<S>, relation: map<S, set<S>>, initial: set<S>): (step: set<S>)
  requires initial <= universe
  requires forall s | s in universe :: s in relation && relation[s] <= universe
  ensures step <= universe
{
  set s0, s1 | s0 in initial && s1 in relation[s0] :: s1
}

function ReflexiveTransitiveClosure<S>(universe: set<S>, relation: map<S, set<S>>, initial: set<S>): (closure: set<S>)
  requires initial <= universe
  requires forall s | s in universe :: s in relation && relation[s] <= universe
  decreases universe - initial
  ensures closure <= universe
{
  var next := initial + RelationStep(universe, relation, initial);
  if next <= initial
  then initial
  else ReflexiveTransitiveClosure(universe, relation, next)
}

function NFACharStep<S>(nfa: NFA<S>, current_states: set<S>, next_char: char): (step: set<S>)
  requires WFNFA(nfa)
  requires next_char in nfa.alphabet
  requires current_states <= nfa.states
  ensures step <= nfa.states
{
  set s0, s1 | s0 in current_states && s1 in nfa.char_step[(s0, next_char)] :: s1
}

function NFAStep<S>(nfa: NFA<S>, current_states: set<S>, next_char: char): (step: set<S>)
  requires WFNFA(nfa)
  requires next_char in nfa.alphabet
  requires current_states <= nfa.states
  ensures step <= nfa.states
{
  var closed_current_states := ReflexiveTransitiveClosure(nfa.states, nfa.epsilon_step, current_states);
  NFACharStep(nfa, closed_current_states, next_char)
}

predicate StringInAlphabet(alphabet: set<char>, s: string)
{
  forall c | c in s :: c in alphabet
}

predicate AcceptsFromStates<S>(nfa: NFA<S>, current_states: set<S>, s: string)
  requires WFNFA(nfa)
  requires StringInAlphabet(nfa.alphabet, s)
  requires current_states <= nfa.states
  decreases s
{
  if s == []
  then exists s | s in current_states :: s in nfa.accepting
  else AcceptsFromStates(nfa, NFAStep(nfa, current_states, s[0]), s[1..])
}

predicate Accepts<S>(nfa: NFA<S>, s: string)
  requires WFNFA(nfa)
  requires StringInAlphabet(nfa.alphabet, s)
{
  AcceptsFromStates(nfa, nfa.initial, s)
}

function LanguageOf<S>(nfa: NFA<S>): iset<string>
  requires WFNFA(nfa)
{
  iset s | StringInAlphabet(nfa.alphabet, s) && Accepts(nfa, s)
}

predicate IsRegular<S(!new)>(L: iset<string>)
{
  exists nfa: NFA<S> | WFNFA(nfa) :: L == LanguageOf(nfa)
}

/*
nfa for L:

                     +-a,b-
                     |   /
                     |  /
                     V /
(0) -a-> (1) -a,b-> (2) -a-> ((3))

*/

datatype S = S0 | S1 | S2 | S3

function CharStep(s: S, c: char): set<S>
  requires IsAOrB(c)
{
  match (s, c)
    case (S0, 'a') => {S1}
    case (S0, 'b') => {}
    case (S1, _)   => {S2}
    case (S2, 'a') => {S2, S3}
    case (S2, 'b') => {S2}
    case (S3, _) => {}
}

predicate IsState(s: S)
{
  true
}

function LNFA(): NFA<S>
{
  var alphabet := {'a', 'b'};
  var states := {S0, S1, S2, S3};
  var initial := {S0};
  var accepting := {S3};
  var epsilon_step := map s | IsState(s) :: {};
  var char_step_domain := set s, c | s in states && c in alphabet :: (s, c);
  var char_step := map p | p in char_step_domain :: var (s, c) := p; CharStep(s, c);
  NFA(alphabet, states, initial, accepting, epsilon_step, char_step)
}

lemma AcceptsImpliesInL(s: string)
  requires StringInAlphabet(LNFA().alphabet, s)
  requires Accepts(LNFA(), s)
  ensures InL(s)
{
  var nfa := LNFA();
  var current_states := nfa.initial;
  var s' := s;
  var x := [];
  while s' != []
    invariant StringInAlphabet(nfa.alphabet, s')
    invariant current_states <= nfa.states
    invariant AcceptsFromStates(nfa, current_states, s')
    invariant ContainsOnlyAsAndBs(x)
    invariant S0 in current_states ==> s == s' && x == []
    invariant S1 in current_states ==> s == ['a'] + x + s'
    invariant S2 in current_states ==> x != [] && s == ['a'] + x + s'
    invariant S3 in current_states ==> x != [] && x[..|x|-1] != [] && x[|x|-1] == 'a' &&
                                      s == ['a'] + x + s'

    decreases s'
  {
    if S1 in current_states || S2 in current_states {
      x := x + [s'[0]];
    }
    current_states := NFAStep(nfa, current_states, s'[0]);
    s' := s'[1..];
  }
  var y := x[..|x|-1];
  assert ContainsOnlyAsAndBs(y);  // trigger InL
}

lemma ReflexiveTransitiveClosureEmptyIdentity<S>(universe: set<S>, relation: map<S, set<S>>, initial: set<S>)
  requires initial <= universe
  requires forall s | s in universe :: s in relation && relation[s] == {}
  ensures ReflexiveTransitiveClosure(universe, relation, initial) == initial
{}

lemma LNFAStepIsCharStep(current_states: set<S>, next_char: char)
  requires next_char in LNFA().alphabet
  requires current_states <= LNFA().states
  ensures NFAStep(LNFA(), current_states, next_char) == NFACharStep(LNFA(), current_states, next_char)
{}

lemma InLImpliesAccepts(s: string)
  requires ContainsOnlyAsAndBs(s)
  requires InL(s)
  ensures Accepts(LNFA(), s)
{
  var nfa := LNFA();
  var x :| ContainsOnlyAsAndBs(x) && x != [] && s == ['a'] + x + ['a'];
  assert StringInAlphabet(nfa.alphabet, s);
  assert |s| >= 3;
  calc <== {
    Accepts(nfa, s);
    AcceptsFromStates(nfa, nfa.initial, s);
    <==> AcceptsFromStates(nfa, {S0}, s);
    AcceptsFromStates(nfa, NFAStep(nfa, {S0}, s[0]), s[1..]);
    AcceptsFromStates(nfa, NFACharStep(nfa, {S0}, s[0]), s[1..]);
    {
      assert S1 in nfa.char_step[(S0, s[0])];  // trigger NFACharStep
      assert NFACharStep(nfa, {S0}, s[0]) == {S1};
    }
    AcceptsFromStates(nfa, {S1}, s[1..]);
    {
      assert S2 in nfa.char_step[(S1, s[1])];  // trigger NFACharStep
      assert NFACharStep(nfa, {S1}, s[1]) == {S2};
    }
    AcceptsFromStates(nfa, {S2}, s[2..]);
  }
  assert AcceptsFromStates(nfa, {S2}, s[2..]) ==> Accepts(nfa, s);

  var s' := s[2..];

  assert s == ['a'] + [s[1]] + s';
  var current_states := {S2};
  while |s'| > 1
    invariant |s'| >= 1
    invariant s'[|s'|-1] == 'a'
    invariant StringInAlphabet(nfa.alphabet, s')
    invariant current_states <= nfa.states
    invariant AcceptsFromStates(nfa, current_states, s') ==> Accepts(nfa, s)
    invariant S2 in current_states
    decreases s'
  {
    current_states := NFAStep(nfa, current_states, s'[0]);
    s' := s'[1..];
  }
  assert |s'| == 1;
  assert s' == [s'[0]];
  assert s'[0] == 'a';

  var last_states := NFAStep(nfa, current_states, 'a');
  assert S3 in last_states;

  calc <== {
    AcceptsFromStates(nfa, current_states, s');
    AcceptsFromStates(nfa, current_states, ['a']);
    AcceptsFromStates(nfa, last_states, []);
    true;
  }
}

lemma LIsRegular()
  ensures IsRegular<S>(L())
{
  var nfa := LNFA();
  assert WFNFA(nfa);
  forall s: string
    ensures s in LanguageOf(nfa) <==> s in L()
  {
    if s in LanguageOf(nfa) {
      AcceptsImpliesInL(s);
      assert s in L();
    }
    if s in L() {
      InLImpliesAccepts(s);
      assert s in LanguageOf(nfa);
    }
  }
  assert LanguageOf(nfa) == L();
}
