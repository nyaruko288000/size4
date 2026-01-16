#include <iostream>
#include <vector>
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <array>
#include <omp.h>

// ========== 1. 基础定义 ==========
// 广群用 uint32_t 表示
// Bit layout: Cell(r, c) is at bits [2*(4*r + c) : 2*(4*r + c) + 1]

constexpr uint32_t N = 4;
constexpr uint32_t NUM_PERMUTATIONS = 24; // 4!

// 预计算表结构
struct PermutationInfo {
    // map_val[v] = sigma(v) : 值如何变化
    uint8_t map_val[N]; 
    
    // map_pos[flat_idx] = flattened_new_pos : 单元格位置如何变化
    // flat_idx = 4*r + c
    // flattened_new_pos = 4*sigma(r) + sigma(c)
    uint8_t map_pos[N * N];
};

std::array<PermutationInfo, NUM_PERMUTATIONS> perms;

// ========== 2. 预计算逻辑 ==========
void precompute_permutations() {
    std::array<uint8_t, N> p = {0, 1, 2, 3};
    int idx = 0;
    do {
        // 记录值的映射 sigma(x)
        for(int i=0; i<N; ++i) perms[idx].map_val[i] = p[i];
        
        // 记录位置的映射 (r, c) -> (sigma(r), sigma(c))
        for(int r=0; r<N; ++r) {
            for(int c=0; c<N; ++c) {
                int original_flat = 4 * r + c;
                int transformed_flat = 4 * p[r] + p[c];
                perms[idx].map_pos[original_flat] = transformed_flat;
            }
        }
        idx++;
    } while (std::next_permutation(p.begin(), p.end()));
}

// ========== 3. 核心：同构检查 (Hot Path) ==========
// 检查 g 是否是其同构类中的字典序最小代表
// 加上 inline 让编译器尽可能内联优化
inline bool is_canonical(uint32_t g) {
    // 遍历所有非恒等置换 (跳过第0个，因为它是恒等的，变换后等于自己)
    // 我们需要确保 g <= transform(g) 对所有置换成立
    
    for (int k = 1; k < NUM_PERMUTATIONS; ++k) {
        uint32_t transformed_g = 0;
        const auto& P = perms[k];

        // 手动展开循环或依赖编译器展开。对于固定 N=4，编译器通常会展开。
        // 我们要构造 transformed_g:
        // 新位置 P.map_pos[i] 的值 = P.map_val[ 原位置 i 的值 ]
        
        for (int i = 0; i < 16; ++i) {
            // 提取原始 g 在位置 i 的 2-bit 值
            // (g >> (2*i)) & 3
            uint32_t original_val = (g >> (i << 1)) & 3;
            
            // 转换该值
            uint32_t new_val = P.map_val[original_val];
            
            // 放到新位置
            // new_pos = P.map_pos[i]
            // shift = 2 * new_pos
            transformed_g |= (new_val << (P.map_pos[i] << 1));
        }

        // 核心检查：如果发现任何一个变体比当前 g 小，说明 g 不是老大
        if (transformed_g < g) {
            return false;
        }
    }
    return true;
}

// ========== 4. 主函数与并行流 ==========
int main() {
    // 初始化
    precompute_permutations();
    
    // 准备写入文件
    // 注意：为了并行写入，我们需要每个线程有自己的 buffer，最后合并
    // 或者简单点：每个线程写一个临时文件，最后 cat 起来 (Actions 上很快)
    
    printf("Starting enumeration for Size 4 Groupoids...\n");
    
    // 我们将 32 位空间切分。
    // 为了防止 buffer 溢出，分块处理。
    // OpenMP 会自动处理循环分配。
    
    const uint64_t TOTAL = 1ULL << 32;
    
    #pragma omp parallel
    {
        // 每个线程独立的输出文件名
        int thread_id = omp_get_thread_num();
        std::string filename = "chunk_" + std::to_string(thread_id) + ".bin";
        std::ofstream out(filename, std::ios::binary);
        
        // 每个线程独立的计数
        uint64_t local_count = 0;
        
        // 动态调度，块大小设大一点减少开销
        #pragma omp for schedule(dynamic, 1048576)
        for (uint64_t i = 0; i < TOTAL; ++i) {
            uint32_t g = (uint32_t)i;
            if (is_canonical(g)) {
                out.write(reinterpret_cast<const char*>(&g), sizeof(g));
                local_count++;
            }
        }
        out.close();
        printf("Thread %d finished. Found: %lu\n", thread_id, local_count);
    }
    
    printf("All threads finished. Merging files is up to you (or use cat).\n");
    
    return 0;
}
