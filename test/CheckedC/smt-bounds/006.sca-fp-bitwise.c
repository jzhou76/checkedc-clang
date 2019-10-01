// Example of false-positive bug report by static analyzer
//
// The expression ((x & 1) && ((x & 1) ^ 1)) always evaluates to 0.
// This expression is not handled by internal solver of the analyzer
// and therefore both paths are considered, and in the _then_ branch
// a null dereference is reported.
//
// This bug report can be refuted by Z3

int foo(int x)
{
    int *z = 0;
    if ((x & 1) && ((x & 1) ^ 1))
        return *z;
    return 0;
}

