#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>

// ==================== Size 2 ====================
constexpr int N2 = 2;
constexpr int NUM_PERM2 = 2;

struct Perm2 {
    uint8_t map_val[N2];
    uint8_t map_pos[N2 * N2];
};

std::array<Perm2, NUM_PERM2> perms2;

void precompute_perm2() {
    std::array<uint8_t, N2> p = {0, 1};
    int idx = 0;
    do {
        for (int i = 0; i < N2; ++i) perms2[idx].map_val[i] = p[i];
        for (int r = 0; r < N2; ++r)
            for (int c = 0; c < N2; ++c)
                perms2[idx].map_pos[N2 * r + c] = N2 * p[r] + p[c];
        idx++;
    } while (std::next_permutation(p.begin(), p.end()));
}

inline bool is_canonical2(uint8_t g) {
    for (int k = 1; k < NUM_PERM2; ++k) {
        uint8_t t = 0;
        const auto& P = perms2[k];
        for (int i = 0; i < 4; ++i) {
            uint8_t val = (g >> i) & 1;
            uint8_t new_val = P.map_val[val];
            t |= (new_val << P.map_pos[i]);
        }
        if (t < g) return false;
    }
    return true;
}

void generate_size2(const char* filename) {
    precompute_perm2();
    std::vector<int8_t> models;
    
    for (int g = 0; g < 16; ++g) {
        if (is_canonical2(g)) {
            for (int i = 0; i < 4; ++i)
                models.push_back((g >> i) & 1);
        }
    }
    
    std::ofstream out(filename, std::ios::binary);
    int32_t count = models.size() / 4;
    out.write(reinterpret_cast<char*>(&count), sizeof(count));
    out.write(reinterpret_cast<char*>(models.data()), models.size());
    out.close();
    
    std::cout << "[Size2] Generated " << count << " canonical models\n";
}

// ==================== Size 3 ====================
constexpr int N3 = 3;
constexpr int NUM_PERM3 = 6;

struct Perm3 {
    uint8_t map_val[N3];
    uint8_t map_pos[N3 * N3];
};

std::array<Perm3, NUM_PERM3> perms3;

void precompute_perm3() {
    std::array<uint8_t, N3> p = {0, 1, 2};
    int idx = 0;
    do {
        for (int i = 0; i < N3; ++i) perms3[idx].map_val[i] = p[i];
        for (int r = 0; r < N3; ++r)
            for (int c = 0; c < N3; ++c)
                perms3[idx].map_pos[N3 * r + c] = N3 * p[r] + p[c];
        idx++;
    } while (std::next_permutation(p.begin(), p.end()));
}

void generate_size3(const char* filename) {
    precompute_perm3();
    
    uint32_t pow3[9];
    pow3[0] = 1;
    for (int i = 1; i < 9; ++i) pow3[i] = pow3[i-1] * 3;
    
    std::vector<int8_t> models;
    
    for (uint32_t g = 0; g < 19683; ++g) {
        bool canonical = true;
        for (int k = 1; k < NUM_PERM3 && canonical; ++k) {
            uint32_t t = 0;
            const auto& P = perms3[k];
            for (int i = 0; i < 9; ++i) {
                uint32_t val = (g / pow3[i]) % 3;
                t += P.map_val[val] * pow3[P.map_pos[i]];
            }
            if (t < g) canonical = false;
        }
        
        if (canonical) {
            for (int i = 0; i < 9; ++i)
                models.push_back((g / pow3[i]) % 3);
        }
    }
    
    std::ofstream out(filename, std::ios::binary);
    int32_t count = models.size() / 9;
    out.write(reinterpret_cast<char*>(&count), sizeof(count));
    out.write(reinterpret_cast<char*>(models.data()), models.size());
    out.close();
    
    std::cout << "[Size3] Generated " << count << " canonical models\n";
}

int main() {
    generate_size2("models2.bin");
    generate_size3("models3.bin");
    std::cout << "\nAll done.\n";
    return 0;
}
