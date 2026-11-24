// KMZI, laboratory 1, variant 2: GF(2^8), BelT block cipher, BelT-GCM.
// Build with a C++20 compiler and run: the program checks the algorithms.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <exception>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string_view>
#include <vector>

using Byte = std::uint8_t;
using Block = std::array<Byte, 16>;
using Key = std::array<Byte, 32>;
using Nonce = std::array<Byte, 12>;

// 1. Arithmetic in GF(2^8). Variant 2 uses modulus 0x14D.
struct GF256 {
    std::uint16_t polynomial;
    explicit GF256(std::uint16_t p) : polynomial(p) {
        if (p < 0x100 || p > 0x1ff || (p & 1u) == 0)
            throw std::invalid_argument("expected a degree-8 polynomial with nonzero constant term");
    }
    static Byte add(Byte a, Byte b) { return Byte(a ^ b); }

    Byte multiply(Byte a, Byte b) const {
        Byte result = 0;
        for (unsigned i = 0; i < 8; ++i) {
            result ^= Byte(a & Byte(0u - (b & 1u)));
            const Byte reduce = Byte(0u - (a >> 7));
            a = Byte((a << 1) ^ (Byte(polynomial & 0xffu) & reduce));
            b >>= 1;
        }
        return result;
    }

    Byte inverse(Byte a) const { // a^254; inverse(0) = 0 by convention.
        const Byte a2 = multiply(a, a), a4 = multiply(a2, a2);
        const Byte a8 = multiply(a4, a4), a16 = multiply(a8, a8);
        const Byte a32 = multiply(a16, a16), a64 = multiply(a32, a32);
        const Byte a128 = multiply(a64, a64);
        Byte v = multiply(a128, a64);
        v = multiply(v, a32); v = multiply(v, a16); v = multiply(v, a8);
        return multiply(multiply(v, a4), a2);
    }

    std::array<Byte, 256> make_sbox() const {
        std::array<Byte, 256> sbox{};
        for (unsigned i = 0; i < 256; ++i) {
            const Byte x = inverse(Byte(i));
            sbox[i] = Byte(x ^ std::rotl(x, 1) ^ std::rotl(x, 2) ^
                           std::rotl(x, 3) ^ std::rotl(x, 4) ^ 0x63u);
        }
        return sbox; // Demonstrates field-derived S-box; BelT uses its own H.
    }
};

// GHASH multiplication in GF(2^128), modulo x^128+x^7+x^2+x+1.
Block gf128_multiply(const Block& x, const Block& y) {
    Block product{}, v = y;
    for (unsigned bit = 0; bit < 128; ++bit) {
        const Byte mask = Byte(0u - ((x[bit / 8] >> (7 - bit % 8)) & 1u));
        for (unsigned j = 0; j < 16; ++j) product[j] ^= Byte(v[j] & mask);
        const Byte reduce = Byte(0u - (v[15] & 1u));
        Byte carry = 0;
        for (unsigned j = 0; j < 16; ++j) {
            const Byte next = Byte(v[j] & 1u);
            v[j] = Byte((v[j] >> 1) | (carry << 7));
            carry = next;
        }
        v[0] ^= Byte(0xe1u & reduce);
    }
    return product;
}

void ghash_step(Block& state, const Block& h, const Block& input) {
    for (unsigned i = 0; i < 16; ++i) state[i] ^= input[i];
    state = gf128_multiply(state, h);
}

// 2. BelT block encryption. Its fixed H permutation is rebuilt without a
// secret-indexed table: every call runs the same recurrence and masked XOR.
Byte equal_mask(Byte a, Byte b) {
    const std::uint32_t d = std::uint32_t(a ^ b);
    return Byte(0u - ((d - 1u) >> 31)); // 0xFF iff a == b.
}

Byte belt_h(Byte x) {
    Byte answer = Byte(0x8eu & equal_mask(x, 11)); // H[10]=0; H[11]=0x8E.
    Byte t = 0x8e;
    for (unsigned index = 12; index <= 265; ++index) {
        for (unsigned i = 0; i < 116; ++i) {
            const Byte feedback = Byte(((t >> 6) ^ (t >> 5) ^ (t >> 1) ^ t) & 1u);
            t = Byte((feedback << 7) | (t >> 1));
        }
        answer ^= Byte(t & equal_mask(x, Byte(index)));
    }
    return answer;
}

std::uint32_t read32(const Byte* p) {
    return std::uint32_t(p[0]) | (std::uint32_t(p[1]) << 8) |
           (std::uint32_t(p[2]) << 16) | (std::uint32_t(p[3]) << 24);
}

void write32(Byte* p, std::uint32_t x) {
    for (unsigned i = 0; i < 4; ++i) { p[i] = Byte(x); x >>= 8; }
}

struct Belt {
    std::array<std::uint32_t, 8> key{};
    explicit Belt(const Key& bytes) {
        for (unsigned i = 0; i < 8; ++i) key[i] = read32(bytes.data() + 4 * i);
    }
    static std::uint32_t g(std::uint32_t x, int rotation) {
        std::uint32_t y = 0;
        for (unsigned i = 0; i < 4; ++i)
            y |= std::uint32_t(belt_h(Byte(x >> (8 * i)))) << (8 * i);
        return std::rotl(y, rotation);
    }
    Block encrypt(const Block& input) const {
        auto a = read32(input.data()), b = read32(input.data() + 4);
        auto c = read32(input.data() + 8), d = read32(input.data() + 12);
        for (unsigned round = 1; round <= 8; ++round) {
            const auto k = [this, round](unsigned step) {
                return key[((round - 1) * 7 + step) % 8];
            };
            b ^= g(a + k(0), 5);
            c ^= g(d + k(1), 21);
            a -= g(b + k(2), 13);
            const auto e = g(b + c + k(3), 21) ^ round;
            b += e; c -= e;
            d += g(c + k(4), 13);
            b ^= g(a + k(5), 21);
            c ^= g(d + k(6), 5);
            std::swap(a, b); std::swap(c, d); std::swap(b, c);
        }
        Block output{};
        write32(output.data(), b); write32(output.data() + 4, d);
        write32(output.data() + 8, a); write32(output.data() + 12, c);
        return output;
    }
};

// 3. GCM for a 96-bit nonce and 128-bit tag. Never repeat a nonce with a key.
void check_length(std::size_t aad, std::size_t text) {
    constexpr std::uint64_t max_bits_bytes = std::numeric_limits<std::uint64_t>::max() / 8;
    if (aad > max_bits_bytes || text > max_bits_bytes ||
        text / 16 + (text % 16 != 0) > std::uint64_t{0xfffffffeu})
        throw std::length_error("GCM message too long");
}

Block counter0(const Nonce& nonce) {
    Block block{};
    std::copy(nonce.begin(), nonce.end(), block.begin());
    block[15] = 1;
    return block;
}

void increment32(Block& counter) {
    for (int i = 15; i >= 12; --i) if (++counter[i] != 0) break;
}

void write64(Byte* output, std::uint64_t x) {
    for (int i = 7; i >= 0; --i) { output[i] = Byte(x); x >>= 8; }
}

void ghash_data(Block& state, const Block& h, const std::vector<Byte>& data) {
    for (std::size_t offset = 0; offset < data.size(); offset += 16) {
        Block chunk{};
        const auto count = std::min<std::size_t>(16, data.size() - offset);
        std::copy_n(data.data() + offset, count, chunk.begin());
        ghash_step(state, h, chunk);
    }
}

Block make_tag(const Belt& belt, const Block& j0,
               const std::vector<Byte>& aad, const std::vector<Byte>& ciphertext) {
    const Block h = belt.encrypt(Block{});
    Block state{};
    ghash_data(state, h, aad);
    ghash_data(state, h, ciphertext);
    Block lengths{};
    write64(lengths.data(), std::uint64_t(aad.size()) * 8);
    write64(lengths.data() + 8, std::uint64_t(ciphertext.size()) * 8);
    ghash_step(state, h, lengths);
    const Block pad = belt.encrypt(j0);
    for (unsigned i = 0; i < 16; ++i) state[i] ^= pad[i];
    return state;
}

std::vector<Byte> counter_xor(const Belt& belt, Block counter,
                              const std::vector<Byte>& input) {
    std::vector<Byte> output(input.size());
    for (std::size_t offset = 0; offset < input.size(); offset += 16) {
        increment32(counter);
        const Block stream = belt.encrypt(counter);
        const auto count = std::min<std::size_t>(16, input.size() - offset);
        for (std::size_t i = 0; i < count; ++i) output[offset + i] = Byte(input[offset + i] ^ stream[i]);
    }
    return output;
}

bool equal_tag(const Block& a, const Block& b) {
    Byte difference = 0;
    for (unsigned i = 0; i < 16; ++i) difference |= Byte(a[i] ^ b[i]);
    return difference == 0; // OR is essential: XORing all differences can cancel.
}

struct Sealed { std::vector<Byte> ciphertext; Block tag; };

Sealed seal(const Belt& belt, const Nonce& nonce,
            const std::vector<Byte>& aad, const std::vector<Byte>& plaintext) {
    check_length(aad.size(), plaintext.size());
    const Block j0 = counter0(nonce);
    auto ciphertext = counter_xor(belt, j0, plaintext);
    const Block tag = make_tag(belt, j0, aad, ciphertext);
    return {std::move(ciphertext), tag};
}

bool open(const Belt& belt, const Nonce& nonce, const std::vector<Byte>& aad,
          const std::vector<Byte>& ciphertext, const Block& tag,
          std::vector<Byte>& plaintext) {
    check_length(aad.size(), ciphertext.size());
    const Block j0 = counter0(nonce);
    if (!equal_tag(tag, make_tag(belt, j0, aad, ciphertext))) return false;
    plaintext = counter_xor(belt, j0, ciphertext); // Never release unauthenticated text.
    return true;
}

unsigned hex_digit(char c) {
    if (c >= '0' && c <= '9') return unsigned(c - '0');
    if (c >= 'a' && c <= 'f') return unsigned(c - 'a') + 10;
    if (c >= 'A' && c <= 'F') return unsigned(c - 'A') + 10;
    throw std::invalid_argument("invalid hex digit");
}

std::vector<Byte> from_hex(std::string_view s) {
    if (s.size() % 2) throw std::invalid_argument("odd number of hex digits");
    std::vector<Byte> result(s.size() / 2);
    for (std::size_t i = 0; i < result.size(); ++i)
        result[i] = Byte((hex_digit(s[2 * i]) << 4) | hex_digit(s[2 * i + 1]));
    return result;
}

template <std::size_t N> std::array<Byte, N> fixed_hex(std::string_view s) {
    const auto bytes = from_hex(s);
    if (bytes.size() != N) throw std::invalid_argument("incorrect hex field length");
    std::array<Byte, N> result{};
    std::copy(bytes.begin(), bytes.end(), result.begin());
    return result;
}

void print_hex(const Byte* data, std::size_t count) {
    for (std::size_t i = 0; i < count; ++i)
        std::cout << std::hex << std::setfill('0') << std::setw(2) << unsigned(data[i]);
    std::cout << std::dec << '\n';
}

void expect(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

void selftest() {
    const GF256 gf(0x14d);
    expect(gf.inverse(0) == 0, "inverse(0)");
    for (unsigned a = 1; a < 256; ++a)
        expect(gf.multiply(Byte(a), gf.inverse(Byte(a))) == 1, "GF inverse");
    const auto sbox = gf.make_sbox();
    expect(belt_h(0) == 0xb1 && belt_h(11) == 0x8e &&
           belt_h(12) == 0x58 && belt_h(255) == 0x1d,
           "BelT H recurrence");
    std::array<bool, 256> seen{};
    for (Byte x : sbox) { expect(!seen[x], "S-box permutation"); seen[x] = true; }
    const auto aes_sbox = GF256(0x11b).make_sbox();
    expect(aes_sbox[0] == 0x63 && aes_sbox[0x53] == 0xed, "polynomial input");

    const auto key = fixed_hex<32>("E9DEE72C8F0C0FA62DDB49F46F739647"
                                   "06075316ED247A3739CBA38303A98BF6");
    const auto plain = fixed_hex<16>("B194BAC80A08F53B366D008E584A5DE4");
    const auto expected = fixed_hex<16>("69CCA1C93557C9E3D66BC3E0FA88FA6E");
    expect(Belt(key).encrypt(plain) == expected, "official BelT block vector");
    const auto h = fixed_hex<16>("66e94bd4ef8a2c3b884cfa59ca342b2e");
    const auto x = fixed_hex<16>("0388dace60b6a392f328c2b971b2fe78");
    expect(gf128_multiply(x, h) == fixed_hex<16>("5e2ec746917062882c85b0685353deb7"),
           "GHASH multiplication vector");

    const Belt belt(key);
    const auto nonce = fixed_hex<12>("000102030405060708090a0b");
    const auto aad = from_hex("10111213141516");
    const auto message = from_hex("202122232425262728292a2b2c2d2e2f30313233343536");
    auto packet = seal(belt, nonce, aad, message);
    std::vector<Byte> recovered;
    expect(open(belt, nonce, aad, packet.ciphertext, packet.tag, recovered), "GCM open");
    expect(recovered == message, "GCM round trip");
    auto bad_tag = packet.tag;
    bad_tag[0] ^= 1;
    expect(!open(belt, nonce, aad, packet.ciphertext, bad_tag, recovered), "tag tamper");
    expect(recovered == message, "invalid tag changed plaintext output");
    Block wrong_a{}, wrong_b{};
    wrong_a[0] = wrong_a[1] = 1;
    expect(!equal_tag(wrong_a, wrong_b), "two tag differences cancelled");
    const auto empty = seal(belt, nonce, {}, {});
    expect(empty.tag == belt.encrypt(counter0(nonce)), "empty GCM tag");
    std::cout << "ciphertext="; print_hex(packet.ciphertext.data(), packet.ciphertext.size());
    std::cout << "tag="; print_hex(packet.tag.data(), packet.tag.size());
    std::cout << "All checks passed\n";
}

int main() {
    try {
        selftest();
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 2;
    }
}
