#include <bits/stdc++.h>
using namespace std;

const int MAX = 110;
const long long INF = 1e18;

int n, m, origem, destino;
long long capacidade[MAX][MAX];
vector<int> adj[MAX];

long long bfs(int s, int t, vector<int>& pai) {
    fill(pai.begin(), pai.end(), -1);
    pai[s] = -2;
    queue<pair<int, long long>> q;
    q.push({s, INF});

    while (!q.empty()) {
        int atual = q.front().first;
        long long fluxo = q.front().second;
        q.pop();

        for (int prox : adj[atual]) {
            if (pai[prox] == -1 && capacidade[atual][prox] > 0) {
                pai[prox] = atual;
                long long novo_fluxo = min(fluxo, capacidade[atual][prox]);
                if (prox == t)
                    return novo_fluxo;
                q.push({prox, novo_fluxo});
            }
        }
    }

    return 0;
}

long long edmonds_karp(int s, int t) {
    long long fluxo_total = 0;
    vector<int> pai(n + 1);
    long long novo_fluxo;

    while ((novo_fluxo = bfs(s, t, pai)) > 0) {
        fluxo_total += novo_fluxo;
        int atual = t;
        while (atual != s) {
            int anterior = pai[atual];
            capacidade[anterior][atual] -= novo_fluxo;
            capacidade[atual][anterior] += novo_fluxo;
            atual = anterior;
        }
    }

    return fluxo_total;
}

int main() {
    cin >> n >> m;
    cin >> origem >> destino;

    for (int i = 0; i < m; i++) {
        int u, v;
        long long c;
        cin >> u >> v >> c;
        capacidade[u][v] += c;
        adj[u].push_back(v);
        adj[v].push_back(u);
    }

    cout << edmonds_karp(origem, destino) << endl;

    return 0;
}
