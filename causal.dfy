// A transition relation modeling causal delivery via vector clocks.

type positive = n: nat | n > 0
  witness 1

// The number of nodes in the system. Used as the length of the vector clocks.
const n_nodes: positive

// A node is identified by its VC index.
type Node = n: nat | 0 <= n < n_nodes

// ---------------------------------------------------------------------------

// The whole system is parameterized by an "underlying state machine", which
// consists of state and messages. Our system will guarantee that this state
// machine is executed in a causally consistent way.

// Type of underlying messages
type UnderlyingPayload

// We require the underlying system to store the sender's index in the payload
// and provide us with this function to extract it.
function UnderlyingPayloadSrc(p: UnderlyingPayload): Node

// Type of underlying local state.
type UnderlyingData

// The initial states of the underlying state machine.
predicate UnderlyingInit(tid: Node, d: UnderlyingData)

// We require the underlying state machine to be "initializable", ie, that at
// least one initial state exists (for each node).
//
// While not strictly required, this allows us to prove that our global causal
// delivery system is also globally initializable, which helps us convince
// ourselves that we are not reasoning vacuously.
lemma UnderlyingInitExists(tid: Node) returns (d: UnderlyingData)
  ensures UnderlyingInit(tid, d)

// Externally-controlled action of the underlying state machine that is invoked
// whenever a message is received.
predicate UnderlyingRecv(tid: Node, recv: UnderlyingPayload, d: UnderlyingData, d': UnderlyingData)

// Internally controlled action of the underlying state machine that can send a
// message.
predicate UnderlyingSend(tid: Node, d: UnderlyingData, d': UnderlyingData, send: UnderlyingPayload)

// ---------------------------------------------------------------------------

// General utilities, some relating to UnderlyingData.

predicate TotalIMap<A(!new),B>(m: imap<A, B>)
{
  forall x :: x in m
}

predicate AlwaysTrue<A>(x: A) {
  true
}

function ConstantIMap<A(!new), B>(y: B): imap<A, B> {
  imap x | AlwaysTrue(x) :: y
}

lemma UnderlyingDataNonEmpty()
  ensures exists d: UnderlyingData :: AlwaysTrue(d)
{
  var d_ignore := UnderlyingInitExists(0);
  assert AlwaysTrue(d_ignore);
}

function ArbitraryUnderlyingData(): UnderlyingData {
  UnderlyingDataNonEmpty();
  var d :| true; d
}


// ---------------------------------------------------------------------------

// Vector clocks

// The sequence of n zeros.
function method Zeros(n: nat): seq<nat>
{
  seq(n, _ => 0)
}

function MaxNat(n1: nat, n2: nat): nat {
  if n1 < n2 then
    n2
  else
    n1
}

// A vector clock is a sequence of nats of length `n_nodes`
type VC = s: seq<nat> | |s| == n_nodes
  witness Zeros(n_nodes)

// Operations on Vector clocks:

// Join
function VCMerge(vc1: VC, vc2: VC): VC {
  seq(n_nodes, i requires 0 <= i < n_nodes => MaxNat(vc1[i], vc2[i]))
}

// Increment the entry at index `tid`.
function IncVC(tid: Node, vc: VC): VC {
  seq(n_nodes, i requires 0 <= i < n_nodes => if i == tid then vc[i] + 1 else vc[i])
}

// The "characteristic vector" of `tid`, ie, the VC of all 0s except at index
// `tid`, where the entry is 1 instead.
function VCChar(tid: Node): VC {
  seq(n_nodes, i requires 0 <= i < n_nodes => if i == tid then 1 else 0)
}

// Ordering on VCs
predicate VCLe(vc1: VC, vc2: VC) {
  forall tid: Node :: vc1[tid] <= vc2[tid]
}

// Strict ordering
predicate VCLt(vc1: VC, vc2: VC) {
  VCLe(vc1, vc2) && vc1 != vc2
}

// ---------------------------------------------------------------------------

// The *local* causal delivery system.

// Messages wrap underlying payloads with a VC.
datatype Message = Message(vc: VC, payload: UnderlyingPayload)

// Convenience function to grab the sender of a Message from its payload.
function MessageSender(m: Message): Node {
  UnderlyingPayloadSrc(m.payload)
}

// The local state of our system. A buffer, a VC, and the underlying state.
datatype LocalState = LocalState(buffer: set<Message>, now: VC, data: UnderlyingData)

// Now we set up the local state machine.

// First, the initial local states.
predicate LocalInit(tid: Node, ls: LocalState) {
  && ls.buffer == {}
  && ls.now == VCChar(tid)
  && UnderlyingInit(tid, ls.data)
}

// The local system is "initializable", ie, there exists at least one initial
// local state (for each node).
//
// This ensures we aren't reasoning vacuously by assuming false invariants.
lemma LocalInitExists(tid: Node) returns (ls: LocalState)
  ensures LocalInit(tid, ls)
{
  var d := UnderlyingInitExists(tid);
  ls := LocalState({}, VCChar(tid), d);
}

// Now we list the local steps.

// Externally controlled action to receive and buffer a message.
predicate LocalRecv(recv: Message, s: LocalState, s': LocalState) {
  s' == s.(buffer := {recv} + s.buffer)
}

// Check that a message is deliverable.
//
// TODO: Is this right? James made it up from first principles.
predicate Deliverable(src: Node, msg_vc: VC, local_vc: VC) {
  && (forall i: Node | i != src :: local_vc[i] >= msg_vc[i])
  && local_vc[src] + 1 == msg_vc[src]
}

// Internally controlled action that delivers a buffered message.
predicate LocalDeliver(tid: Node, m: Message, s: LocalState, s': LocalState) {
  && m in s.buffer
  && Deliverable(UnderlyingPayloadSrc(m.payload), m.vc, s.now)
  && UnderlyingRecv(tid, m.payload, s.data, s.data)
  && s' == s.(buffer := s.buffer - {m}, now := VCMerge(s.now, m.vc))
}

// Internally controlled action that sends a message.
predicate LocalSend(tid: Node, s: LocalState, s': LocalState, send: Message) {
  && UnderlyingSend(tid, s.data, s'.data, send.payload)
  && send.vc == s.now
  && UnderlyingPayloadSrc(send.payload) == tid
  && s' == s.(now := IncVC(tid, s.now), data := s'.data)
}


// ---------------------------------------------------------------------------

// The *global* causal delivery system.

// The local state of each node.
type LocalStateMap = m: imap<Node, LocalState> | TotalIMap(m)
  ghost witness ConstantIMap(LocalState({}, Zeros(n_nodes), ArbitraryUnderlyingData()))

// The global state of our system is the local states plus the network (modeled
// as the set of sent messages) plus a ghost history tracking delivered messages.
//
// This way of doing things is a bit of a hack, but avoids having to set up any
// notion of execution or event, or defining happens before on send/deliver
// events. Instead, we take HB <==> VC as a modeling-level axiom.
datatype GlobalState = GlobalState(
  local_states: LocalStateMap,
  sent: set<Message>,
  delivered: set<(Node, Message, VC)>
)

// Now we set up the global state machine.

// First, the global initial states.
predicate GlobalInit(gs: GlobalState) {
  && (forall tid :: LocalInit(tid, gs.local_states[tid]))
  && gs.sent == {}
  && gs.delivered == {}
}

// The global system is "initializable", ie, at least one initial state exists.
//
// This ensures we aren't reasoning vacuously by assuming false invariants about
// the set of initial states.
lemma GlobalInitExists() returns (gs: GlobalState)
  ensures GlobalInit(gs)
{
  var local_states: LocalStateMap;
  var sent: set<Message> := {};
  var delivered: set<(Node, Message, VC)> := {};

  var tid: int := 0;
  while tid < n_nodes
    invariant 0 <= tid <= n_nodes
    invariant forall j | 0 <= j < tid :: LocalInit(j, local_states[j])
  {
    var ls := LocalInitExists(tid);
    local_states := local_states[tid := ls];
    tid := tid + 1;
  }

  gs := GlobalState(local_states, sent, delivered);
}

// Now the global steps of the system.
predicate GlobalStep(gs: GlobalState, gs': GlobalState) {
  || GlobalSend(gs, gs')
  || GlobalRecv(gs, gs')
  || GlobalDeliver(gs, gs')
}

// As is idiomatic in Ironfleet style, we separate out the existential
// quantifier from the rest of the predicate. We use primed names for predicates
// that have the existential variables passed in as additional parameters.
//
// This helps in writing proofs during debugging, because it gives a shorthand
// name to do the body of the existential quantifier and thus avoids copy
// pasting it, but it is not essential.

predicate GlobalRecv(gs: GlobalState, gs': GlobalState) {
  exists tid, m ::
    GlobalRecv'(tid, m, gs, gs')
}

// A step that selects a message causes it to be received (ie, buffered) by a
// node.
predicate GlobalRecv'(tid: Node, m: Message, gs: GlobalState, gs': GlobalState) {
  && m in gs.sent
  && LocalRecv(m, gs.local_states[tid], gs'.local_states[tid])
  && gs' == gs.(local_states := gs.local_states[tid := gs'.local_states[tid]])
}

predicate GlobalSend(gs: GlobalState, gs': GlobalState) {
  exists tid, m ::
    GlobalSend'(tid, gs, gs', m)
}

// A step to send a message.
predicate GlobalSend'(tid: Node, gs: GlobalState, gs': GlobalState, m: Message) {
  && LocalSend(tid, gs.local_states[tid], gs'.local_states[tid], m)
  && gs' == gs.(local_states := gs.local_states[tid := gs'.local_states[tid]],
               sent := gs.sent + {m})
}

predicate GlobalDeliver(gs: GlobalState, gs': GlobalState) {
  exists tid, m ::
    GlobalDeliver'(tid, m, gs, gs')
}

// A step to deliver a buffered message.
predicate GlobalDeliver'(tid: Node, m: Message, gs: GlobalState, gs': GlobalState) {
  && LocalDeliver(tid, m, gs.local_states[tid], gs'.local_states[tid])
  && gs' == gs.(local_states := gs.local_states[tid := gs'.local_states[tid]],
               delivered := gs.delivered + {(tid, m, gs.local_states[tid].now)})
}


// ---------------------------------------------------------------------------

// Proofs


// Causal Delivery: If m1 sent before m2 was sent, and m2 is delivered at node
// N, then m1 is also delivered at node N.
//
// NOTE: We ignore delivery of a message to its sender. In practice, you could
// just have the implementation immediately locally deliver the message to the
// underlying state machine on the sender when the message is sent. This would
// complicate our proof slightly, because it mixes the "sending" and
// "delivering" cases of the proof. So we ignore it.


// If m1 was sent before m2 was sent, and m2 is delivered at node `receiver`
// (and receiver is not the sender of m1), then m1 is also delivered at node
// `receiver`.
//
// Our top-level theorem is that this is an invariant of the global system.
predicate GlobalCausalDelivery(gs: GlobalState) {
  forall receiver, m1, m2, vc_deliver2 ::
    && (receiver, m2, vc_deliver2) in gs.delivered
    && m1 in gs.sent
    && VCLt(m1.vc, m2.vc)
    && MessageSender(m1) != receiver
    ==>
    exists vc_deliver1 ::
      (receiver, m1, vc_deliver1) in gs.delivered
}

// To prove the theorem, we need to strengthen it into an inductive invariant.
//
// Ours has several conjuncts, primarily related to how VCs in the system
// interact, as well as the ghost delivery log.
predicate Inv(gs: GlobalState) {
  && GlobalCausalDelivery(gs)
  && SentVCs(gs)
  && DeliveredMessagesWereSent(gs)
  && BufferedMessagesWereSent(gs)
  && NodeVCs(gs)
  && NodeHasSeenSendersMessages(gs)
  && SentMessageUniqueness(gs)
}

// Quick reminder/check that our Inv should imply GlobalCausalDelivery.
//
// In this case it is obvious because GlobalCausalDelivery is a conjunct, but as
// the invariant gets long, it's easy to accidentally remove that conjunct and
// not notice.
lemma InvImpliesGlobalCausalDelivery(gs: GlobalState)
  requires Inv(gs)
  ensures GlobalCausalDelivery(gs)
{}

// Here are the definitions of each conjunct of the inductive invariant.

// If `receiver`'s local VC has a clock value in its `sender` index greater than
// or equal to x, then `receiver` has delivered `sender`'s x-th message.
predicate NodeHasSeenSendersMessages(gs: GlobalState) {
  forall receiver: Node, m ::
    var sender := MessageSender(m);
    && m in gs.sent
    && m.vc[sender] <= gs.local_states[receiver].now[sender]
    && sender != receiver
    ==>
    exists vc_deliver ::
      (receiver, m, vc_deliver) in gs.delivered
}

// If a node has delivered a message, then that node's VC is greater than or
// equal to the message's VC.
predicate DeliveredVCs(gs: GlobalState) {
  forall receiver, m, vc | (receiver, m, vc) in gs.delivered ::
   VCLe(m.vc, gs.local_states[receiver].now)
}

// A node's own index in its own VC is greater than that of any sent message.
predicate SentVCs(gs: GlobalState) {
  forall m, tid: Node | m in gs.sent ::
    m.vc[tid] < gs.local_states[tid].now[tid]
}

// A node's own index in its own VC is greater than that of any other node's.
predicate NodeVCs(gs: GlobalState) {
  forall tid: Node, tid_owner: Node | tid != tid_owner ::
    gs.local_states[tid].now[tid_owner] < gs.local_states[tid_owner].now[tid_owner]
}

// Every delivered message was sent.
predicate DeliveredMessagesWereSent(gs: GlobalState) {
  forall receiver, m, vc | (receiver, m, vc) in gs.delivered ::
    m in gs.sent
}

// Every buffered message was sent.
predicate BufferedMessagesWereSent(gs: GlobalState) {
  forall receiver: Node, m | m in gs.local_states[receiver].buffer ::
    m in gs.sent
}

// Messages are uniquely identified by (sender, sender's clock entry).
predicate SentMessageUniqueness(gs: GlobalState) {
  forall m1, m2 | m1 in gs.sent && m2 in gs.sent ::
    && MessageSender(m1) == MessageSender(m2)
    && m1.vc[MessageSender(m1)] == m2.vc[MessageSender(m1)]
    ==> m1 == m2
}

// Now here is a proof by induction that Inv is an invariant of the transition
// system (GlobalInit, GlobalStep).

lemma InvInit(gs: GlobalState)
  requires GlobalInit(gs)
  ensures Inv(gs)
{}

lemma InvInductive(gs: GlobalState, gs': GlobalState)
  requires GlobalStep(gs, gs')
  requires Inv(gs)
  ensures Inv(gs')
{
  if GlobalSend(gs, gs') {
    InvSend(gs, gs');
  }
  if GlobalDeliver(gs, gs') {
    InvDeliver(gs, gs');
  }
}

// The induction step uses the following two lemmas about the "interesting" steps.

// NOTE: Although these proofs are "trivial" (they have empty lemma bodies),
// during the debugging process they become highly nontrivial. This is typical
// of Dafny proofs.

lemma InvSend(gs: GlobalState, gs': GlobalState)
  requires GlobalSend(gs, gs')
  requires Inv(gs)
  ensures Inv(gs')
{}

lemma InvDeliver(gs: GlobalState, gs': GlobalState)
  requires GlobalDeliver(gs, gs')
  requires Inv(gs)
  ensures Inv(gs')
{}

// That's it!

// In a more complete development, we could set up a notion of execution as a
// sequence of global states and state and prove that GlobalCausalDelivery is
// true in every state of every execution. But the hard part of that proof is
// just the inductive argument above, so we omit the rest.
