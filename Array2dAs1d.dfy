// RUN: /compile:0 /nologo /rlimit:10000000 /printTooltips /verifySnapshots:3

method foo(input: array<int>, rows:int, cols:int)
requires input != null 
requires rows > 0 && cols > 0
requires rows * cols == input.Length
{
   var i := 0;
   while i < rows
    invariant 0 <= i <= rows
   {
     var j := 0;
     while j < cols
        invariant 0 <= j <= cols;
     {
        assert input.Length == rows * cols;
        assert i < rows;
        assert j < cols;
        assert i * cols < rows * cols;
        assert i <= rows - 1;
        assert cols > 0;
        assert cols * i <= cols * (rows - 1);
        assert i * cols <= (rows - 1) * cols;
       var s := input[i*cols + j];
       j := j + 1;
     }
     i := i + 1;
   }
}
