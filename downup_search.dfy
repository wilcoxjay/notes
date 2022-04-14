predicate method downup_search(down: int, up: int)
  requires down >= 0 || up <= 0
  decreases if down >= 0 then down else -up
{
  down == 0 || (up != 0 && downup_search(down - 1, up + 1))
}

predicate method ge0(n: int) {
  downup_search(n, n)
}

lemma downup_search_correct(down: int, up: int)
  requires down >= 0 || up <= 0
  decreases if down >= 0 then down else -up
  ensures
      downup_search(down, up)
    <==>
      down >= 0 && (up <= 0 ==> down <= -up)
{}

lemma ge0_correct(n: int)
  ensures ge0(n) <==> n >= 0
{
  downup_search_correct(n, n);
}
