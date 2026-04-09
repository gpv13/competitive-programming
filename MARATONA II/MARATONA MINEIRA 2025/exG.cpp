#include <bits/stdc++.h>
using namespace std;
using ll = long long;
using pii = pair<ll, int>;
const ll INF = (ll)1e18;

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int N, C, P;
    cin >> N >> C >> P;

    // Total de vértices em H = 3N (indexados de 1 a 3N)
    int total = 3 * N;
    // adj[u] = lista de pares (v, peso) para cada aresta u → v
    vector<vector<pii>> adj(total + 1);

    // 1) Lê arestas de carro (Gc) e insere em H2 (vértices N+1 .. 2N)
    // Gc é direcionado: cada (a → b, custo c) vira (N+a → N+b, custo c)
    for (int i = 0; i < C; ++i) {
        int a, b;
        ll c;
        cin >> a >> b >> c;
        // camada H2: offset = N
        adj[N + a].push_back({c, N + b});
    }

    // 2) Lê arestas a pé (Gp) e insere em H1 e em H3
    // Gp é bidirecional: cada (a ↔ b, custo p)
    //   → H1: (a → b, p) e (b → a, p), em indices [1..N]
    //   → H3: (2N + a → 2N + b, p) e (2N + b → 2N + a, p)
    for (int i = 0; i < P; ++i) {
        int a, b;
        ll p;
        cin >> a >> b >> p;
        // H1 = [1 .. N]
        adj[a].push_back({p, b});
        adj[b].push_back({p, a});
        // H3 = [2N+1 .. 3N], index base 2N
        adj[2 * N + a].push_back({p, 2 * N + b});
        adj[2 * N + b].push_back({p, 2 * N + a});
    }

    // 3) Arestas de custo 0 para subir de camada:
    //    H1 → H2 : u → (N+u), peso 0
    //    H2 → H3 : (N+u) → (2N+u), peso 0
    for (int u = 1; u <= N; ++u) {
        // H1 → H2
        adj[u].push_back({0, N + u});
        // H2 → H3
        adj[N + u].push_back({0, 2 * N + u});
    }

    // 4) Executa Dijkstra em H a partir do vértice 1 (H1) até o vértice 3N (H3, índice 2N+N)
    vector<ll> dist(total + 1, INF);
    vector<bool> visited(total + 1, false);
    priority_queue<pii, vector<pii>, greater<pii>> pq;

    dist[1] = 0;
    pq.push({0, 1});  // (dist, vértice)

    while (!pq.empty()) {
        auto [d_u, u] = pq.top();
        pq.pop();
        if (visited[u]) continue;
        visited[u] = true;

        for (auto &[w_uv, v] : adj[u]) {
            if (dist[v] > d_u + w_uv) {
                dist[v] = d_u + w_uv;
                pq.push({dist[v], v});
            }
        }
    }

    // 5) A resposta é a distância até o vértice N em H3, que é (2N + N) = 3N
    ll ans = dist[3 * N];
    if (ans >= INF) {
        cout << "-1\n"; // ou algum valor que indique não alcançável, conforme o enunciado
    } else {
        cout << ans << "\n";
    }

    return 0;
}
