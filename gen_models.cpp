#include <iostream>
#include <fstream>
#include <vector>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <omp.h>

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

// ==================== Size 4 ====================
constexpr int N4 = 4;
constexpr int NUM_PERM4 = 24;

struct Perm4 {
    uint8_t map_val[N4];
    uint8_t map_pos[N4 * N4];
    uint8_t shift[N4 * N4];
};

std::array<Perm4, NUM_PERM4> perms4;

void precompute_perm4() {
    std::array<uint8_t, N4> p = {0, 1, 2, 3};
    int idx = 0;
    do {
        for (int i = 0; i < N4; ++i) perms4[idx].map_val[i] = p[i];
        for (int r = 0; r < N4; ++r)
            for (int c = 0; c < N4; ++c) {
                int pos = N4 * r + c;
                int new_pos = N4 * p[r] + p[c];
                perms4[idx].map_pos[pos] = new_pos;
                perms4[idx].shift[pos] = new_pos << 1;
            }
        idx++;
    } while (std::next_permutation(p.begin(), p.end()));
}

inline bool is_canonical4(uint32_t g) {
    for (int k = 1; k < NUM_PERM4; ++k) {
        uint32_t t = 0;
        const auto& P = perms4[k];
        for (int i = 0; i < 16; ++i) {
            uint32_t val = (g >> (i << 1)) & 3;
            t |= (P.map_val[val] << P.shift[i]);
        }
        if (t < g) return false;
    }
    return true;
}

void generate_size4(const char* filename) {
    precompute_perm4();
    
    std::cout << "[Size4] Starting enumeration...\n";
    
    const uint64_t TOTAL = 1ULL << 32;
    std::vector<std::vector<int8_t>> thread_buffers;
    
    #pragma omp parallel
    {
        #pragma omp single
        thread_buffers.resize(omp_get_num_threads());
        
        int tid = omp_get_thread_num();
        thread_buffers[tid].reserve(1024 * 1024 * 16);
        
        #pragma omp for schedule(dynamic, 1048576)
        for (uint64_t i = 0; i < TOTAL; ++i) {
            uint32_t g = (uint32_t)i;
            if (is_canonical4(g)) {
                for (int j = 0; j < 16; ++j)
                    thread_buffers[tid].push_back((g >> (j << 1)) & 3);
            }
        }
    }
    
    std::ofstream out(filename, std::ios::binary);
    int32_t total_count = 0;
    for (auto& buf : thread_buffers) total_count += buf.size() / 16;
    
    out.write(reinterpret_cast<char*>(&total_count), sizeof(total_count));
    for (auto& buf : thread_buffers)
        out.write(reinterpret_cast<char*>(buf.data()), buf.size());
    out.close();
    
    std::cout << "[Size4] Generated " << total_count << " canonical models\n";
}

int main() {
    generate_size2("models2.bin");
    generate_size3("models3.bin");
    generate_size4("models4.bin");
    std::cout << "\nAll done.\n";
    return 0;
}
