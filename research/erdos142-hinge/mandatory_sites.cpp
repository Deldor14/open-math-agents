#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>

using Mask = std::uint64_t;
static int capacity[65];
static unsigned char local_capacity[1U << 12];

bool find_set(Mask candidates, Mask reflected, int target, Mask &witness) {
    if (target == 0) return true;
    while (__builtin_popcountll(candidates) >= target) {
        const int low = __builtin_ctzll(candidates);
        const Mask normalized = candidates >> low;
        const int range = 64 - __builtin_clzll(normalized);
        if (capacity[range] < target) return false;
        int bound = 0;
        for (Mask chunk = normalized; chunk; chunk >>= 12)
            bound += local_capacity[chunk & 4095];
        if (bound < target) return false;
        Mask bit = Mask(1) << low;
        candidates ^= bit;
        // A chosen point a is stored at bit 63-a. Shifting moves that bit
        // to 2*low-a, the forbidden third point when low is selected.
        const Mask excluded = low < 32 ? reflected >> (63-2*low) : reflected << (2*low-63);
        if (find_set(candidates & ~excluded, reflected | (Mask(1) << (63-low)), target-1, witness)) {
            witness |= bit;
            return true;
        }
    }
    return false;
}

int main(int argc, char** argv) {
    const int maximum = argc > 1 ? std::atoi(argv[1]) : 45;
    if (maximum < 1 || maximum > 63) return 2;
    for (unsigned s = 0; s < 4096; ++s) {
        int best = __builtin_popcount(s);
        for (int d = 1; 2*d < 12; ++d) {
            unsigned starts = s & (s >> d) & (s >> (2*d));
            if (!starts) continue;
            unsigned p = starts & -starts;
            best = std::max({local_capacity[s ^ p], local_capacity[s ^ (p << d)],
                             local_capacity[s ^ (p << (2*d))]});
            break;
        }
        local_capacity[s] = best;
    }
    for (int n = 1; n <= maximum; ++n) {
        Mask full = (Mask(1) << n) - 1, witness = 0;
        capacity[n] = capacity[n-1] + 1;
        if (!find_set(full,0,capacity[n],witness)) --capacity[n];
        // Away from a jump or its immediate successor, three translates suffice.
        if (n >= 3 && capacity[n] == capacity[n-2]) continue;
        if (capacity[n] > capacity[n-1]) {
            std::cout << "jump " << n << " " << capacity[n] << std::endl;
            continue;
        }
        Mask mandatory = full;
        for (int i = 0; i < n && mandatory; ++i) {
            if (!(mandatory & (Mask(1) << i))) continue;
            witness = 0;
            if (find_set(full ^ (Mask(1) << i),0,capacity[n],witness)) mandatory &= witness;
        }
        std::cout << "next " << n << " " << capacity[n] << " " << mandatory << std::endl;
    }
}
