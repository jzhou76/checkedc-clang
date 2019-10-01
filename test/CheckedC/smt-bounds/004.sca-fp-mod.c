// Example of false-positive bug report by static analyzer
//
// The condition (i % width == 0) is always true and "base" always gets a value.
// But the analyzer reports use of uninitialized of "base"
//
// This bug report can be refuted by Z3


#include <assert.h>

void foo(unsigned width) {
    assert( width > 0 );
    int base;
    int i = 0;

    if ( i % width == 0 )
        base = 1;

    assert( base == 1 );
}
