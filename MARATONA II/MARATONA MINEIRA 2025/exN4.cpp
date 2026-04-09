#include <bits/stdc++.h>
using namespace std;


struct SuffixArray {
    string S;
    int n;
    vector<int> SA;   // SA[i] = índice onde começa o i-ésimo menor sufixo
    vector<int> rank; // rank[i] = posição do sufixo que começa em i na ordem ordenada

    SuffixArray(string s) : S(s), n(s.size()) {
        SA.resize(n);
        rank.resize(n);
        constructSA();
    }

    void constructSA() {
        // 1. Inicialização: Rank baseado apenas no primeiro caractere
        for (int i = 0; i < n; i++) {
            SA[i] = i;
            rank[i] = S[i];
        }

        // 2. Loop de Doubling: A cada passo k, ordenamos sufixos baseados nos primeiros 2*k caracteres
        // k começa em 1 e dobra: 1, 2, 4, 8...
        for (int k = 1; k < n; k <<= 1) {
            
            // Função lambda para comparar dois sufixos usando o rank atual e o rank do "pulo" k
            auto cmp = [&](int i, int j) {
                if (rank[i] != rank[j]) return rank[i] < rank[j]; // Compara primeira parte
                
                // Compara segunda parte (o pulo de k posições)
                int ri = (i + k < n) ? rank[i + k] : -1; // -1 se passar do fim da string
                int rj = (j + k < n) ? rank[j + k] : -1;
                return ri < rj;
            };

            // Ordena o array de índices com base na comparação definida acima
            sort(SA.begin(), SA.end(), cmp);

            // Recalcula os ranks baseados na nova ordem
            vector<int> tmp(n);
            tmp[SA[0]] = 0;
            for (int i = 1; i < n; i++) {
                // Se o sufixo atual é idêntico ao anterior (nas primeiras 2*k letras), mantém o rank
                // Caso contrário, incrementa o rank
                tmp[SA[i]] = tmp[SA[i - 1]] + (cmp(SA[i - 1], SA[i]) ? 1 : 0);
            }
            rank = tmp;

            // Otimização: Se todos os ranks forem distintos (0 a n-1), já está ordenado
            if (rank[SA[n - 1]] == n - 1) break;
        }
    }

    int getRank(int idx) {
        return rank[idx];
    }
};

void solve() {
    string s;

    cin >> s;
    int n = s.size();

    char min_global = s[0];
    for (char c : s) min_global = min(min_global, c);


    int L = 0;
    while (L < n && s[L] == min_global) {
        L++;
    }

    if (L >= n) {
        cout << s << endl;
        return;
    }

    string s_rev = s;
    reverse(s_rev.begin(), s_rev.end());
    

    SuffixArray sa(s_rev);

    char min_sufixo = s[L];
    for (int i = L; i < n; i++) min_sufixo = min(min_sufixo, s[i]);

    // cout << min_sufixo << endl; 

    int best_R = -1;
    int best_rank = 1e9 + 7;

    for (int i = L+1; i < n; i++) {
        if (s[i] == min_sufixo) {            
            // cout << "entrou\n";
            int indice_na_invertida = n - 1 - i;
            
            int rank_atual = sa.getRank(indice_na_invertida);

            if (rank_atual < best_rank) {
                best_rank = rank_atual;
                best_R = i;
            }
        }
    }
    // cout << L << " " << best_R << endl;
    if (best_R != -1) {
        reverse(s.begin() + L, s.begin() + best_R + 1);
    }

    cout << s << endl;
}

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    solve();

    return 0;
}