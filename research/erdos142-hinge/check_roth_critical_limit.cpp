// Integer enclosures for the k=3, lambda=1 fixed point and its free fraction.
// Build with c++ -O2 -std=c++17 and run the binary. No external libraries.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>

using i64 = std::int64_t;
using wide = __int128_t;
constexpr int grid = 4096;
constexpr int rounds = 40;
constexpr i64 unit = 1000000;
constexpr i64 fine = 1000000000000LL;
constexpr i64 subdivisions = 16384;
constexpr i64 denominator = grid * unit * unit;

struct Bounds {
    i64 lo;
    i64 hi;
};

static wide ceil_div(wide a, wide b) {
    return (a+b-1)/b;
}

// The lower approximation uses (1-x/m)^m and the upper one (1+x/m)^(-m).
static i64 exponential_bound(i64 numerator, bool upper) {
    const wide d = wide(denominator)*subdivisions;
    assert(numerator >= 0 && numerator <= 2*denominator);
    wide current = upper ? ceil_div(wide(fine)*d, d+numerator)
                         : wide(fine)*(d-numerator)/d;
    for (i64 m = subdivisions; m > 1; m /= 2) {
        assert(m%2 == 0);
        const wide square = current*current;
        current = upper ? ceil_div(square, fine) : square/fine;
    }
    return i64(upper ? ceil_div(current*unit, fine) : current*unit/fine);
}

static Bounds child_range(const std::vector<Bounds>& q, int parent, int step, int offset) {
    const int first = std::max(0, parent + offset*step + std::min(0,offset));
    const int last = std::min(grid-1, parent + offset*step + std::max(0,offset));
    assert(first <= last);
    Bounds out = q[first];
    for (int i=first+1; i<=last; ++i) {
        out.lo = std::min(out.lo, q[i].lo);
        out.hi = std::max(out.hi, q[i].hi);
    }
    return out;
}

// Numerators for integral K(q,q) with denominator grid * unit^2.
static std::vector<Bounds> integrate(const std::vector<Bounds>& q) {
    std::vector<Bounds> sums(grid);
    constexpr std::array<int,3> left{0,1,2};
    constexpr std::array<int,3> right{2,1,0};
    for (int i=0; i<(grid+1)/2; ++i) {
        Bounds total{0,0};
        for (int anchor=0; anchor<3; ++anchor) {
            for (int j=0; j<grid; ++j) {
                if ((left[anchor] && i+1<=left[anchor]*j) ||
                    (right[anchor] && i+right[anchor]*j>=grid)) break;
                const bool full = i >= left[anchor]*(j+1)
                                  && i+1+right[anchor]*(j+1) <= grid;
                i64 lo = 1, hi = 1;
                for (int child=0; child<3; ++child) {
                    if (child==anchor) continue;
                    const Bounds values = child_range(q,i,j,child-anchor);
                    lo *= values.lo;
                    hi *= values.hi;
                }
                if (full) total.lo += lo;
                total.hi += hi;
            }
        }
        sums[i] = sums[grid-1-i] = total;
    }
    return sums;
}

// Enclose -log(x/unit) by the positive series for 2*atanh((1-q)/(1+q)).
static Bounds log_bounds(i64 x) {
    assert(3*x>=unit && x<=unit);
    const wide top = wide(unit-x)*fine;
    const Bounds t{i64(top/(unit+x)), i64(ceil_div(top,unit+x))};
    const Bounds t2{i64(wide(t.lo)*t.lo/fine), i64(ceil_div(wide(t.hi)*t.hi,fine))};
    assert(t2.hi <= fine/2);
    Bounds power=t, total{0,0};
    for (int m=0; m<20; ++m) {
        total.lo += 2*power.lo/(2*m+1);
        total.hi += i64(ceil_div(2*power.hi,2*m+1));
        power.lo = i64(wide(power.lo)*t2.lo/fine);
        power.hi = i64(ceil_div(wide(power.hi)*t2.hi, fine));
    }
    total.hi += 4*power.hi;
    return total;
}

int main() {
    std::vector<Bounds> q(grid, Bounds{0,unit});
    for (int r=0; r<rounds; ++r) {
        const auto means = integrate(q);
        for (int i=0; i<grid; ++i) {
            q[i].lo = std::max(q[i].lo, exponential_bound(means[i].hi, false));
            q[i].hi = std::min(q[i].hi, exponential_bound(means[i].lo, true));
            assert(0<=q[i].lo && q[i].lo<=q[i].hi && q[i].hi<=unit);
        }
    }
    wide lo = 0, hi = 0;
    for (int i=0; i<grid; ++i) {
        lo += wide(q[i].lo)*(3*fine+2*log_bounds(q[i].lo).lo);
        hi += wide(q[i].hi)*(3*fine+2*log_bounds(q[i].hi).hi);
    }
    const wide divisor = wide(3)*grid*fine;
    std::cout << "Free fraction in millionths: [" << i64(lo/divisor) << ", "
              << i64(ceil_div(hi,divisor)) << "]\n";
}
