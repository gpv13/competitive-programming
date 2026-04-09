#include <iostream>
#include <vector>

using namespace std;

const int MOD = 998244353;
const int MAX = 400005; // Tamanho máximo para (N + M)

long long fat[MAX];
long long invFat[MAX];

// Função para exponenciação modular: (base^exp) % MOD
// Usada para calcular o inverso modular
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

// Inverso Modular: Calcula 1/n % MOD
long long modInverse(long long n) {
    return power(n, MOD - 2);
}

// Pré-calcula fatoriais e seus inversos para responder O(1)
void precompute() {
    fat[0] = 1;
    invFat[0] = 1;
    for (int i = 1; i < MAX; i++) {
        fat[i] = (fat[i - 1] * i) % MOD;
        invFat[i] = modInverse(fat[i]);
    }
}

// Função de Combinação: nCr = n! / (r! * (n-r)!)
long long nCr(int n, int r) {
    if (r < 0 || r > n) return 0;
    return fat[n] * invFat[r] % MOD * invFat[n - r] % MOD;
}

// --- O que você pediu: Função para o N-ésimo Número de Catalão ---
// Fórmula: 1/(n+1) * C(2n, n)
long long catalan(int n) {
    long long combinacao = nCr(2 * n, n);
    long long inverso_n_mais_1 = modInverse(n + 1);
    return (combinacao * inverso_n_mais_1) % MOD;
}

int main() {
    // Otimização de I/O
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    precompute(); // Prepara os fatoriais antes de começar

    int n, m;
    if (cin >> n >> m) {
        // SOLUÇÃO DO SEU PROBLEMA
        // Total de caminhos - Caminhos Ruins (Reflexão)
        // Total = C(n + m, m)
        // Ruins = C(n + m, m - 1)
        
        long long total = nCr(n + m, m);
        long long ruins = nCr(n + m, m - 1);

        // Subtração em módulo (adicionamos MOD antes de tirar o resto para evitar negativos)
        long long resposta = (total - ruins + MOD) % MOD;

        cout << resposta << endl;
    }

    return 0;
}