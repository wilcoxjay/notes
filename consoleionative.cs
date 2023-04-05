using System;
using System.IO;

namespace _module {
  public partial class __default {
    public static void WriteLine(Dafny.ISequence<Dafny.Rune> line) {
      Console.WriteLine(line.ToVerbatimString(false));
    }
  
    public static Dafny.ISequence<Dafny.Rune> ReadLine() {
      var line = Console.ReadLine();
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(line);
    }
  }
}