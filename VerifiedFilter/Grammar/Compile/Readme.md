# Compiling the Memoization Table

Here we show how the memoization table is compiled.
The implementation of `Regex.derivatives` will not terminate and is declared `partial`.
This has been proven by others to terminate and be a finite list, but our implementation is missing smart constructors and the formal proof of finiteness.
The rest of the implementation `Regex.compile` does terminate and shows that if `Regex.derivatives` is finite then so will is the memoization table size.
