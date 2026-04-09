#include<bits/stdc++.h>
using namespace std;

// DIJKSTRA - O((V + E) log V)
// A lista de adjacência 'adj' deve armazenar pares {peso, vertice}.
vector<long long int> dijkstra(long long int s, long long int n, const vector<vector<pair<long long int, long long int>>>& adj, long long int k) {
    const long long int INF = LLONG_MAX; // Usar um valor grande como infinito
    vector<long long int> dist(n, INF);
    priority_queue<pair<long long int, long long int>, vector<pair<long long int, long long int>>, greater<pair<long long int, long long int>>> pq;

    dist[s] = 0;
    pq.push({0, s}); // Fila de prioridade armazena {distancia, vertice}

    while (!pq.empty()) {
        auto [d, u] = pq.top();
        pq.pop();

        if (d > dist[u]) {
            continue; // Já encontramos um caminho mais curto para 'u'
        }

        for (auto [v, w] : adj[u]) { // Para cada vizinho 'v' de 'u' com peso 'w'
            if (dist[u] + w < dist[v]) {
                dist[v] = dist[u] + w;
                pq.push({dist[v], v});
            }
        }
    }
    return dist;
}

int main(){

    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    long long int n, m, k;
    cin >> n >> m >> k;
    vector<vector<pair<long long int, long long int>>> adj(n+k+1);
    for(long long int i=0;i<m;i++){

        long long int c , u, v;
        cin >> u >> v >> c;
        adj[u].push_back({v, c});
        adj[v].push_back({u, c});

    }
    for(long long int i=1;i<=n;i++){

        long long int num;
        cin >> num;
        for(long long int j=0;j<num;j++){
            long long int type, p;
            cin >> type >> p;
            adj[i].push_back({n+type, p});
            adj[n+type].push_back({i, 0});
        }
    }
    
    vector<long long int> banana = dijkstra(1, n + k + 1, adj, k);
    cout << banana[n] << endl;

    return 0;
}