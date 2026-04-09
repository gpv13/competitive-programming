#include <iostream>
#include <vector>

using namespace std;

const int MOD = 998244353;
const int MAX = 400005;

long long fat[MAX];
long long invFat[MAX];

long long power(long long base, long long exp) {
    long long res = 1;
    base %= MOD;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % MOD;
        base = (base * base) % MOD;
        exp /= 2;
    }
    return res;
}


long long modInverse(long long n) {
    return power(n, MOD - 2);
}


void precompute() {
    fat[0] = 1;
    invFat[0] = 1;
    for (int i = 1; i < MAX; i++) {
        fat[i] = (fat[i - 1] * i) % MOD;
        invFat[i] = modInverse(fat[i]);
    }
}


long long nCr(int n, int r) {
    if (r < 0 || r > n) return 0;
    return fat[n] * invFat[r] % MOD * invFat[n - r] % MOD;
}


int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    precompute();

    int n, m;
    if (cin >> n >> m) {

        
        long long total = nCr(n + m, m);
        long long ruins = nCr(n + m, m - 1);

        long long resposta = (total - ruins + MOD) % MOD;

        cout << resposta << endl;
    }

    return 0;
}