#include <bits/stdc++.h>
using namespace std;

#define MOD 1000000007LL

long long C[1005][1005];

// Preenche o triângulo de Pascal para evitar divisões
void precompute() {
    for (int i = 0; i <= 1000; i++) {
        C[i][0] = 1;
        for (int j = 1; j <= i; j++) {
            C[i][j] = (C[i - 1][j - 1] + C[i - 1][j]) % MOD;
        }
    }
}

long long nCrEfficiente(long long n, long long r) {
    if (r < 0 || r > n) return 0;
    if (r == 0 || r == n) return 1;
    
    // Propriedade: C(n, r) == C(n, n-r)
    if (r > n - r) r = n - r; 

    long long ans = 1;
    for (int i = 1; i <= r; i++) {
        ans = ans * (n - r + i) / i;
    }
    return ans;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string n;
    cin >> n;

    int k;
    cin >> k;
    if(k==0) {cout << "1" << endl; return 0;}
    if(k==1){cout << n.size()-1 << endl; return 0;}
    int dp[1001];
    dp[0] = 0;
    dp[1] = 1;
    for(int i=2;i<=1000;i++){
        dp[i] = dp[__builtin_popcount(i)] + 1;
    }

    // for(auto a : dp) cout << a << endl;
    set<int> nums;
    for(int i=1;i<=1000;i++){
        if(dp[i] == k) nums.insert(i);
    }

    long long int conta = 0;
    precompute(); 

    for(auto s : nums){
        if(s > n.size()) continue;
        int contaUns = 0;
        for(int i = 0; i < n.size(); i++){
            if(n[i] == '1'){
                int posicoes_restantes = (n.size() - 1) - i;
                int bits_faltantes = s - contaUns;
                
                if(bits_faltantes >= 0 && bits_faltantes <= posicoes_restantes) {
                    conta = (conta + C[posicoes_restantes][bits_faltantes]) % MOD;
                }
                contaUns++;
            }
        }
        if(contaUns == s) conta = (conta + 1) % MOD;
    }
    cout << conta << endl;
    return 0;
}