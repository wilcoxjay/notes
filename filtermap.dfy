datatype Option<T> = None | Some(val: T)

// --------------------------------------------------------------------------------
// Versions of several functional operations on sets that take *pure* functions.
// --------------------------------------------------------------------------------


function Filter<A>(f: A -> bool, s: set<A>): set<A>
{
  set x | x in s && f(x)
}

function Map<A,B>(f: A -> B, s: set<A>): set<B>
{
  set x | x in s :: f(x)
}

function FilterMap<A,B>(f: A -> Option<B>, s: set<A>): set<B>
{
  set x | x in s && f(x).Some? :: f(x).val
}

function FilterMap2<A,B>(f: A -> bool, g: A -> B, s: set<A>): set<B>
{
  set x | x in s && f(x) :: g(x)
}

function MapAll<A,B>(f: A -> Option<B>, s: set<A>): Option<set<B>>
{
  if forall x | x in s :: f(x).Some? then
    Some(set x | x in s :: f(x).val)
  else
    None
}


// --------------------------------------------------------------------------------
// Versions that take *partial* functions.
// --------------------------------------------------------------------------------

function FilterPartial<A>(f: A --> bool, s: set<A>): set<A>
  requires forall x | x in s :: f.requires(x)
{
  set x | x in s && f(x)
}

function MapPartial<A,B>(f: A --> B, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
{
  set x | x in s :: f(x)
}

function FilterMapPartial<A,B>(f: A --> Option<B>, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
{
  set x | x in s && f(x).Some? :: f(x).val
}

function FilterMapPartial2<A,B>(f: A --> bool, g: A --> B, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
  requires forall x | x in s && f(x) :: g.requires(x)
{
  set x | x in s && f(x) :: g(x)
}

function FilterMapKindaPartial2<A,B>(f: A -> bool, g: A --> B, s: set<A>): set<B>
  requires forall x | x in s && f(x) :: g.requires(x)
{
  set x | x in s && f(x) :: g(x)
}

// Implementing a pure FilterMap in terms of a pure Filter and a partial Map
// (and a pure Map).

// Note that since Filter is transparent and defined in terms of a comprehentsion,
// no postcondition is needed for Dafny to see that the arguments to MapPartial
// are good.

// Also note that the calls to pure Filter and pure Map can just as well be
// replaced with their partial counterparts, and the result still verifies.
function FilterMapViaFilterAndMap<A,B>(f: A -> Option<B>, s: set<A>): set<B>
{
  MapPartial((x: Option<B>) requires x.Some? => x.val, Filter((x: Option<B>) => x.Some?, Map(f, s)))
}

// It's not much harder to allow the argument to be partial as well.
// Just need to copy the precondition of MapPartial.
function FilterMapViaFilterAndMapPartial<A,B>(f: A --> Option<B>, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
{
  MapPartial((x: Option<B>) requires x.Some? => x.val, Filter((x: Option<B>) => x.Some?, MapPartial(f, s)))
}


// --------------------------------------------------------------------------------
// Versions that also allow the argument to have a reads effect.
// --------------------------------------------------------------------------------


function FilterPartialReads<A>(f: A ~> bool, s: set<A>): set<A>
  requires forall x | x in s :: f.requires(x)
  reads set x,y | x in s && y in f.reads(x) :: y  // think of this as BigUnion(x | x in s :: f.reads(x))
{
  set x | x in s && f(x)
}

function MapPartialReads<A,B>(f: A ~> B, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
  reads set x,y | x in s && y in f.reads(x) :: y
{
  set x | x in s :: f(x)
}

function FilterMapPartialReads<A,B>(f: A ~> Option<B>, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
  reads set x,y | x in s && y in f.reads(x) :: y
{
  set x | x in s && f(x).Some? :: f(x).val
}

function FilterMapPartialReads2<A,B>(f: A ~> bool, g: A ~> B, s: set<A>): set<B>
  requires forall x | x in s :: f.requires(x)
  reads set x, y | x in s && y in f.reads(x) :: y
  requires forall x | x in s && f(x) :: g.requires(x)
  reads set x, y | x in s && y in g.reads(x) :: y
{
  set x | x in s && f(x) :: g(x)
}

function FilterMapKindaPartialReads2<A,B>(f: A -> bool, g: A ~> B, s: set<A>): set<B>
  requires forall x | x in s && f(x) :: g.requires(x)
  reads set x, y | x in s && y in g.reads(x) :: y
{
  set x | x in s && f(x) :: g(x)
}


// It's worth noting here that all any call to a less-effectful version of these functions
// can be replaced with a call to a more-effectful one for free, because Dafny has no trouble
// proving the preconditions when the argument actually doesn't have the effect.

// Thus, I argue for including only the most-effectful versions, under
// the names Filter, Map, etc.

// The only downside I see to this is opacity of documentation and beginner friendliness.
// (Also, the type error messages will be worse.)
// However, we could be careful in the docs to explain the simple versions first.
// We could also, with some additional effort, teach Dafny to issue a nice error message
// in the case when the arguments being passed have less effects.


// --------------------------------------------------------------------------------
// Imagining multiset comprehensions.
// --------------------------------------------------------------------------------


/*
function Filter<A>(f: A -> bool, m: multiset<A>): multiset<A>
{
  multiset x | x in m && f(x) :: x := m[x]
}

function Map<A,B>(f: A -> B, m: multiset<A>): multiset<B>
{
  multiset x | x in m :: f(x) := m[x]
}

function FilterMap<A,B>(f: A -> Option<B>, m: multiset<A>): multiset<B>
{
  multiset x | x in m && f(x).Some? :: f(x).val
}
*/


// --------------------------------------------------------------------------------
// Prototyping multiset comprehensions by manual encoding as maps to int.
// --------------------------------------------------------------------------------


type multisetish<A> = map<A,int>

function MultisetishFilter<A>(f: A -> bool, m: multisetish<A>): multisetish<A>
{
  map x | x in m && f(x) :: x := m[x]
}

function MultisetishMap<A,B>(f: A -> B, m: multisetish<A>): multisetish<B>
  requires forall x, y | x in m && y in m :: f(x) == f(y) ==> x == y
{
  map x | x in m :: f(x) := m[x]
}

function MultisetishFilterMap<A,B>(f: A -> Option<B>, m: multisetish<A>): multisetish<B>
  requires forall x, y | x in m && y in m :: f(x) == f(y) ==> x == y
{
  map x | x in m && f(x).Some? :: f(x).val := m[x]
}
