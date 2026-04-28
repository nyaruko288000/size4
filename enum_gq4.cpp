#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

using u32 = std::uint32_t;
using u64 = std::uint64_t;

static std::array<std::array<std::uint8_t, 4>, 24> PERMS;

// LUT[perm][half][16-bit-value]
static u32 LUT[24][2][1u << 16];

static void build_perms() {
    std::array<std::uint8_t, 4> p{0, 1, 2, 3};
    int k = 0;

    do {
        PERMS[k++] = p;
    } while (std::next_permutation(p.begin(), p.end()));

    if (k != 24) {
        std::cerr << "Permutation generation error\n";
        std::exit(1);
    }
}

static void build_lut() {
    for (int ip = 0; ip < 24; ++ip) {
        const auto& p = PERMS[ip];

        for (int half = 0; half < 2; ++half) {
            for (u32 w = 0; w < (1u << 16); ++w) {
                u32 result = 0;

                // Each half has 8 cells, each cell uses 2 bits.
                for (int j = 0; j < 8; ++j) {
                    int old_cell = half * 8 + j;

                    int a = old_cell / 4;
                    int b = old_cell % 4;

                    int old_value = static_cast<int>((w >> (2 * j)) & 3u);

                    // Under relabeling p:
                    // new operation satisfies:
                    // U[p(a)][p(b)] = p(T[a][b])
                    int new_a = p[a];
                    int new_b = p[b];
                    int new_value = p[old_value];

                    int new_cell = 4 * new_a + new_b;

                    result |= static_cast<u32>(new_value) << (2 * new_cell);
                }

                LUT[ip][half][w] = result;
            }
        }
    }
}

static inline u32 relabel(int ip, u32 code) {
    return LUT[ip][0][code & 0xffffu]
         | LUT[ip][1][code >> 16];
}

static inline bool is_canonical(u32 code) {
    // PERMS[0] is identity, skip it.
    for (int ip = 1; ip < 24; ++ip) {
        u32 r = relabel(ip, code);
        if (r < code) {
            return false;
        }
    }
    return true;
}

static void flush_buffer(std::ofstream& out, std::vector<u32>& buffer) {
    if (!buffer.empty()) {
        out.write(reinterpret_cast<const char*>(buffer.data()),
                  static_cast<std::streamsize>(buffer.size() * sizeof(u32)));
        buffer.clear();
    }
}

static void worker(u64 start,
                   u64 end,
                   const std::string& filename,
                   u64& out_count) {
    std::ofstream out(filename, std::ios::binary);
    if (!out) {
        std::cerr << "Cannot open shard file: " << filename << "\n";
        std::exit(1);
    }

    constexpr std::size_t BUF_SIZE = 1u << 20; // 1M records = 4 MB
    std::vector<u32> buffer;
    buffer.reserve(BUF_SIZE);

    u64 count = 0;

    for (u64 x = start; x < end; ++x) {
        u32 code = static_cast<u32>(x);

        if (is_canonical(code)) {
            buffer.push_back(code);
            ++count;

            if (buffer.size() >= BUF_SIZE) {
                flush_buffer(out, buffer);
            }
        }
    }

    flush_buffer(out, buffer);
    out_count = count;
}

static void write_u32_le(std::ofstream& out, u32 x) {
    char b[4];
    b[0] = static_cast<char>(x & 0xffu);
    b[1] = static_cast<char>((x >> 8) & 0xffu);
    b[2] = static_cast<char>((x >> 16) & 0xffu);
    b[3] = static_cast<char>((x >> 24) & 0xffu);
    out.write(b, 4);
}

static void write_u64_le(std::ofstream& out, u64 x) {
    char b[8];
    b[0] = static_cast<char>(x & 0xffu);
    b[1] = static_cast<char>((x >> 8) & 0xffu);
    b[2] = static_cast<char>((x >> 16) & 0xffu);
    b[3] = static_cast<char>((x >> 24) & 0xffu);
    b[4] = static_cast<char>((x >> 32) & 0xffu);
    b[5] = static_cast<char>((x >> 40) & 0xffu);
    b[6] = static_cast<char>((x >> 48) & 0xffu);
    b[7] = static_cast<char>((x >> 56) & 0xffu);
    out.write(b, 8);
}

static void write_header(std::ofstream& out, u64 count) {
    // Header layout, 64 bytes:
    //
    // magic:       8 bytes
    // metadata:   24 bytes = 6 * u32
    // count:       8 bytes
    // reserved:   24 bytes
    //
    // total = 8 + 24 + 8 + 24 = 64

    const char magic[8] = {'G', 'Q', '4', 'B', 'I', 'N', '1', '\0'};
    out.write(magic, 8);

    write_u32_le(out, 1);  // version
    write_u32_le(out, 4);  // set size
    write_u32_le(out, 2);  // arity
    write_u32_le(out, 2);  // bits per value
    write_u32_le(out, 4);  // bytes per record
    write_u32_le(out, 0);  // flags

    write_u64_le(out, count);

    char reserved[24]{};
    out.write(reserved, 24);
}

int main(int argc, char** argv) {
    std::string output = "gq4_canonical.bin";

    if (argc >= 2) {
        output = argv[1];
    }

    unsigned num_threads = std::thread::hardware_concurrency();
    if (argc >= 3) {
        num_threads = static_cast<unsigned>(std::stoul(argv[2]));
    }

    if (num_threads == 0) {
        num_threads = 1;
    }

    std::cerr << "Output file: " << output << "\n";
    std::cerr << "Threads: " << num_threads << "\n";

    build_perms();
    build_lut();

    const u64 total_space = 1ull << 32;
    const u64 chunk = total_space / num_threads;

    std::vector<std::thread> threads;
    std::vector<std::string> shards(num_threads);
    std::vector<u64> counts(num_threads, 0);

    for (unsigned tid = 0; tid < num_threads; ++tid) {
        u64 start = chunk * tid;
        u64 end = (tid + 1 == num_threads)
                ? total_space
                : chunk * (tid + 1);

        shards[tid] = output + ".part" + std::to_string(tid);

        std::cerr << "Thread " << tid
                  << ": [" << start << ", " << end << ") -> "
                  << shards[tid] << "\n";

        threads.emplace_back(worker,
                             start,
                             end,
                             shards[tid],
                             std::ref(counts[tid]));
    }

    for (auto& t : threads) {
        t.join();
    }

    u64 total = 0;
    for (u64 c : counts) {
        total += c;
    }

    std::cerr << "Total canonical representatives: " << total << "\n";

    const u64 expected = 178981952ull;
    if (total != expected) {
        std::cerr << "WARNING: expected " << expected
                  << ", got " << total << "\n";
    }

    // Merge shards into final file with header.
    std::ofstream out(output, std::ios::binary);
    if (!out) {
        std::cerr << "Cannot open final output file.\n";
        return 1;
    }

    write_header(out, total);

    std::vector<char> copy_buffer(1u << 20);

    for (unsigned tid = 0; tid < num_threads; ++tid) {
        std::ifstream in(shards[tid], std::ios::binary);
        if (!in) {
            std::cerr << "Cannot open shard: " << shards[tid] << "\n";
            return 1;
        }

        while (in) {
            in.read(copy_buffer.data(),
                    static_cast<std::streamsize>(copy_buffer.size()));
            std::streamsize got = in.gcount();
            if (got > 0) {
                out.write(copy_buffer.data(), got);
            }
        }
    }

    std::cerr << "Done.\n";
    std::cerr << "You may remove shard files: " << output << ".part*\n";

    return 0;
}
