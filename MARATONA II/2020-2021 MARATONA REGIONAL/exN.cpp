#include<bits/stdc++.h>
using namespace std;

using ull = unsigned long long;

// Multiplicação em O(log n) para evitar overflow em 64 bits
ull mul_mod(ull a, ull b, ull m) {
    ull res = 0;
    a %= m;
    while (b) {
        if (b & 1) res = (res + a) % m;
        a = (a + a) % m;
        b >>= 1;
    }
    return res;
}

// Exponenciação binária usando a nossa multiplicação segura
ull binpower(ull base, ull e, ull mod) {
    ull result = 1;
    base %= mod;
    while (e) {
        if (e & 1) result = mul_mod(result, base, mod);
        base = mul_mod(base, base, mod);
        e >>= 1;
    }
    return result;
}

bool miller_rabin(ull n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;

    ull d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }

    static const ull bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (ull a : bases) {
        if (n <= a) break;
        ull x = binpower(a, d, n);
        if (x == 1 || x == n - 1) continue;
        
        bool composite = true;
        for (int r = 1; r < s; r++) {
            x = mul_mod(x, x, n);
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

ull pollard_rho(ull n) {
    if (n % 2 == 0) return 2;
    if (miller_rabin(n)) return n;

    ull x = 2, y = 2, d = 1, c = 1;
    
    // f(x) = (x^2 + c) mod n usando mul_mod
    auto f = [&](ull x, ull n, ull c) {
        return (mul_mod(x, x, n) + c) % n;
    };

    while (d == 1) {
        x = f(x, n, c);
        y = f(f(y, n, c), n, c);
        ull diff = x > y ? x - y : y - x;
        d = __gcd(diff, n);
        
        if (d == n) {
            x = rand() % (n - 2) + 2;
            y = x;
            c = rand() % (n - 1) + 1;
            d = 1;
        }
    }
    return d;
}

void factorize(ull n, map<ull, int>& factors) {
    if (n == 1) return;
    if (miller_rabin(n)) {
        factors[n]++;
        return;
    }
    ull divisor = pollard_rho(n);
    factorize(divisor, factors);
    factorize(n / divisor, factors);
}

int main() {
    ios_base::sync_with_stdio(false); cin.tie(NULL);
    
    ull m, n, k;
    cin >> m >> n >> k;
    map<ull, int> factors;

    for(int i=0;i<n;i++){
        ull aux;
        cin >> aux;
        factorize(aux, factors);
    }
    

    bool first = true;
    for (auto const& [prime, count] : factors) {
        if(!first) cout << " " << prime;
        else cout << prime;

        first = false;
    }
    cout << endl;    

    return 0;
}