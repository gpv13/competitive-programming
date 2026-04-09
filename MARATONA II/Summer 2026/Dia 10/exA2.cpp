#include <bits/stdc++.h>
using namespace std;

typedef long long ll;

// Constantes para Double Hashing
const ll P1 = 31, M1 = 1e9 + 7;
const ll P2 = 37, M2 = 1e9 + 9;
const int MAXN = 300005;

// Vetores globais para evitar realocação
ll h1[MAXN], h2[MAXN];
ll pow1[MAXN], pow2[MAXN];
int n;
string s;

// Inicializa potências e hashes de prefixo
void build_hash() {
    pow1[0] = 1; pow2[0] = 1;
    h1[0] = 0; h2[0] = 0;
    
    for (int i = 0; i < n; i++) {
        pow1[i+1] = (pow1[i] * P1) % M1;
        pow2[i+1] = (pow2[i] * P2) % M2;
        
        h1[i+1] = (h1[i] * P1 + (s[i] - 'A' + 1)) % M1;
        h2[i+1] = (h2[i] * P2 + (s[i] - 'A' + 1)) % M2;
    }
}

// Retorna o par de hash da substring [i, j] (0-based) em O(1)
pair<ll, ll> get_hash(int i, int j) {
    int len = j - i + 1;
    ll v1 = (h1[j+1] - h1[i] * pow1[len]) % M1;
    if (v1 < 0) v1 += M1;
    
    ll v2 = (h2[j+1] - h2[i] * pow2[len]) % M2;
    if (v2 < 0) v2 += M2;
    
    return {v1, v2};
}

// Verifica se existe ALGUMA substring única de tamanho 'len'
bool check(int len) {
    if (len == 0) return false;
    vector<pair<ll, ll>> v;
    v.reserve(n - len + 1);

    // 1. Gera todos os hashes desse tamanho
    for (int i = 0; i <= n - len; i++) {
        v.push_back(get_hash(i, i + len - 1));
    }

    // 2. Ordena para agrupar iguais
    sort(v.begin(), v.end());

    // 3. Procura alguém que apareça apenas 1 vez
    int sz = v.size();
    if (sz == 0) return false;
    if (sz == 1) return true; // Só tem uma substring possível, é única

    // Checa o primeiro
    if (v[0] != v[1]) return true;
    // Checa o último
    if (v[sz-1] != v[sz-2]) return true;

    // Checa o meio
    for (int i = 1; i < sz - 1; i++) {
        if (v[i] != v[i-1] && v[i] != v[i+1]) {
            return true;
        }
    }
    
    return false;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(NULL);

    if (!(cin >> s)) return 0;
    n = s.size();

    build_hash();

    // Busca Binária pelo MENOR tamanho que possui substring única
    // Intervalo [1, N]. Sabemos que N é sempre possível (a string inteira é única).
    int l = 1, r = n;
    int ans_len = n;

    while (l <= r) {
        int mid = (l + r) / 2;
        if (check(mid)) {
            ans_len = mid; // Possível candidato, tenta menor
            r = mid - 1;
        } else {
            l = mid + 1; // Não tem única desse tamanho, precisa aumentar
        }
    }

    // Agora que sabemos o tamanho 'ans_len', precisamos achar 
    // QUAL é a primeira substring única desse tamanho.
    
    // 1. Coleta hashes e índices
    vector<pair<pair<ll, ll>, int>> final_v;
    final_v.reserve(n - ans_len + 1);
    for (int i = 0; i <= n - ans_len; i++) {
        final_v.push_back({get_hash(i, i + ans_len - 1), i});
    }

    // 2. Ordena apenas pelos hashes para contar frequência
    // Precisamos de uma cópia ou estrutura auxiliar para saber quais são únicos
    vector<pair<ll, ll>> sorted_hashes;
    sorted_hashes.reserve(final_v.size());
    for(auto& x : final_v) sorted_hashes.push_back(x.first);
    sort(sorted_hashes.begin(), sorted_hashes.end());

    // 3. Percorre a string original e vê se o hash é único
    for (int i = 0; i <= n - ans_len; i++) {
        pair<ll, ll> cur = get_hash(i, i + ans_len - 1);
        
        // Busca binária (lower_bound) no vetor ordenado para contar ocorrências
        auto it1 = lower_bound(sorted_hashes.begin(), sorted_hashes.end(), cur);
        auto it2 = upper_bound(sorted_hashes.begin(), sorted_hashes.end(), cur);
        
        if (it2 - it1 == 1) { // Frequência exata de 1
            cout << s.substr(i, ans_len) << endl;
            return 0;
        }
    }

    return 0;
}