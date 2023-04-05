method {:axiom} WriteLine(line: string)
method {:axiom} ReadLine() returns (line: string)

method {:main} Main()
{
  WriteLine("what is your name?");
  var name := ReadLine();
  WriteLine("hello, " + name + "!");
}
