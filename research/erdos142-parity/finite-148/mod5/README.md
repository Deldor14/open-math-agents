# At least eight elements in every residue modulo five

Assume T is a 96-point subset of [1,148] without any arithmetic progression of length six. Then every residue class modulo five has at least eight members of T. This exhaustive finite bound uses no published value of r_6.

Index a class by (x−1) mod 5. Its capacity is at most 23: direct enumeration on intervals of lengths 29 and 30 gives respectively 2 and 34 masks with 23 points and zero with 24. Larger masks would contain a 24-point mask. Thus a class with at most three points cannot accommodate a global total of 96. For weights 4, 5, 6 and 7, enumerate every capacity profile and all admissible tuples of masks for the other four classes, then test candidate completions in the sparse class. Reflection reduces its five possible positions to representatives 0, 1 and 3.

At weight seven the three runs covered 81,629,936,016, 81,629,936,016 and 1,078,586,892,020 dense-fiber tuples, respectively. Only one tuple left seven individually admissible positions. No joint completion survived the direct test against all 2,117 progressions. Counts for all twelve cases appear in counts.txt. This is an exhaustive C++ result, not a Lean or DRAT claim. It leaves r_6(148) open.

Reproduce with an optimizing C++17 compiler:

    c++ -O3 -std=c++17 fibers.cpp -o fibers
    c++ -O3 -std=c++17 classify.cpp -o classify
    for L in 29 30; do for w in 23 24; do ./fibers "$L" "$w" >/dev/null; done; done
    for w in 4 5 6 7; do for c in 0 1 3; do ./classify 148 96 "$c" "$w"; done; done
    ./classify 148 95 0 5

The last command is a positive control. It returns an explicit 95-point set with five members in the specified class. The 96-point search uses only exact mask enumeration, arithmetic progressions and the verified fiber caps.
