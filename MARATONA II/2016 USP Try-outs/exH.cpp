#include <iostream>
#include <vector>
#include <map>
#include <cmath>

using namespace std;

// Definindo dois primos grandes para o Double Hashing
const long long MOD1 = 1e9 + 7;
const long long MOD2 = 1e9 + 9;

int main() {
    // Otimização de I/O
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int n, m;
    if (!(cin >> n >> m)) return 0;

    vector<long long> listaTaylor(n);
    for (int i = 0; i < n; i++) cin >> listaTaylor[i];

    vector<long long> listaKaty(m);
    for (int i = 0; i < m; i++) cin >> listaKaty[i];

    // Mapa: Chave é um par {hash1, hash2}, Valor é a máscara de bits
    map<pair<long long, long long>, int> mapTaylor;

    int limitTaylor = 1 << n; // 2^n
    
    // Processando Taylor
    for (int mask = 1; mask < limitTaylor; mask++) {
        long long prod1 = 1;
        long long prod2 = 1;

        for (int bit = 0; bit < n; bit++) {
            if ((mask >> bit) & 1) {
                prod1 = (prod1 * listaTaylor[bit]) % MOD1;
                prod2 = (prod2 * listaTaylor[bit]) % MOD2;
            }
        }
        
        mapTaylor[{prod1, prod2}] = mask;
    }

    int limitKaty = 1 << m; // 2^m
    
    // Processando Katy e procurando match
    for (int mask = 1; mask < limitKaty; mask++) {
        long long prod1 = 1;
        long long prod2 = 1;
        
        for (int bit = 0; bit < m; bit++) {
            if ((mask >> bit) & 1) {
                prod1 = (prod1 * listaKaty[bit]) % MOD1;
                prod2 = (prod2 * listaKaty[bit]) % MOD2;
            }
        }

        // Verifica se existe no mapa da Taylor
        if (mapTaylor.count({prod1, prod2})) {
            int maskTaylor = mapTaylor[{prod1, prod2}];
            
            cout << "Y\n";
            
            // Reconstrução da resposta
            vector<long long> ansT, ansK;
            
            for (int i = 0; i < n; i++) {
                if ((maskTaylor >> i) & 1) ansT.push_back(listaTaylor[i]);
            }
            for (int i = 0; i < m; i++) {
                if ((mask >> i) & 1) ansK.push_back(listaKaty[i]);
            }

            cout << ansT.size() << " " << ansK.size() << "\n";
            
            for (int i = 0; i < ansT.size(); i++) 
                cout << ansT[i] << (i == ansT.size() - 1 ? "" : " ");
            cout << "\n";
            
            for (int i = 0; i < ansK.size(); i++) 
                cout << ansK[i] << (i == ansK.size() - 1 ? "" : " ");
            cout << "\n";

            return 0;
        }
    }

    cout << "N\n";
    return 0;
}