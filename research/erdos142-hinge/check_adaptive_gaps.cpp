// Compile with c++ -std=c++17 -O2. No nonstandard dependencies.
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

namespace {
constexpr int max_length = 62;
std::array<int, max_length + 1> optimum{};

bool can_finish(int length, int budget, std::vector<int>& letters) {
    if (static_cast<int>(letters.size()) == length) return true;
    const int remaining = length - static_cast<int>(letters.size()) - 1;
    const int maximum = budget - optimum[remaining];
    for (int value = 0; value <= maximum; ++value) {
        letters.push_back(value);
        int left_sum = 0, right_sum = 0;
        bool valid = true;
        const int n = static_cast<int>(letters.size());
        for (int width = 1; 2 * width <= n; ++width) {
            right_sum += letters[n - width];
            left_sum += letters[n - 2 * width];
            if (width > 1)
                left_sum += letters[n - 2 * width + 1] - letters[n - width];
            if (left_sum == right_sum) { valid = false; break; }
        }
        if (valid && can_finish(length, budget - value, letters)) return true;
        letters.pop_back();
    }
    return false;
}

int largest_bad_lift(const std::vector<int>& word) {
    std::vector<int> prefix{0};
    for (int x : word) prefix.push_back(prefix.back() + x);
    int largest = 0;
    for (int i = 0; i < static_cast<int>(prefix.size()); ++i)
        for (int j = i + 1; j < static_cast<int>(prefix.size()); ++j)
            for (int k = j + 1; k < static_cast<int>(prefix.size()); ++k) {
                const int index_delta = i + k - 2*j;
                const int excess = 2*prefix[j] - prefix[i] - prefix[k];
                if (index_delta == 0 && excess == 0)
                    throw std::runtime_error("equal-index progression in witness");
                if (index_delta != 0 && excess % index_delta == 0)
                    largest = std::max(largest, excess / index_delta);
            }
    return largest;
}

void certify_template() {
    const std::array<int,30> block{0,1,0,2,0,1,0,3,1,0,2,0,1,0,9,0,1,0,2,0,1,3,0,1,0,2,0,1,0,6};
    if (std::accumulate(block.begin(), block.end(), 0) != 37)
        throw std::runtime_error("template weight");
    for (int start = 0; start < 30; ++start)
        for (int half = 1; half < 30; ++half) {
            int delta = 0;
            for (int j = 0; j < half; ++j)
                delta += block[(start + j) % 30] - block[(start + half + j) % 30];
            if (delta % 10 == 0) throw std::runtime_error("modular collision");
        }
}
} // namespace

int main() {
    certify_template();
    for (int length = 1; length <= max_length; ++length) {
        int bound = 0;
        for (int split = 1; split < length; ++split)
            bound = std::max(bound, optimum[split] + optimum[length - split]
                                    + (2 * split == length));
        std::vector<int> witness;
        while (!can_finish(length, bound, witness)) ++bound;
        optimum[length] = bound;
        const int last_bad = largest_bad_lift(witness);
        if ((length == 32 && last_bad > 7) || (length == 62 && last_bad > 10))
            throw std::runtime_error("unexpected conflicting lift");
        std::cout << length << ' ' << bound << ' ' << last_bad << '\n';
    }
    if (optimum[32] != 35 || optimum[62] != 73)
        throw std::runtime_error("unexpected minimum");
}
