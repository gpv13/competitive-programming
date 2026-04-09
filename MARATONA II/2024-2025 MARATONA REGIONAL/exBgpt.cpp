#include <bits/stdc++.h>
using namespace std;

const int OFFSET = 1000000; // deslocamento para filmes
const int MAXV = OFFSET + 200; // atores + filmes
vector<vector<int>> adj(MAXV);

vector<int> parent;
vector<bool> visited;

bool dfs(int u, int target) {
    if (u == target) return true;
    visited[u] = true;
    for (int v : adj[u]) {
        if (!visited[v]) {
            parent[v] = u;
            if (dfs(v, target)) return true;
        }
    }
    return false;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int N, M;
    cin >> N >> M;

    // construir grafo bipartido
    for (int i = 1; i <= N; i++) {
        int num; cin >> num;
        int film = OFFSET + i;
        for (int j = 0; j < num; j++) {
            int actor; cin >> actor;
            adj[actor].push_back(film);
            adj[film].push_back(actor);
        }
    }

    int Q;
    cin >> Q;
    while (Q--) {
        int x, y;
        cin >> x >> y;

        visited.assign(MAXV, false);
        parent.assign(MAXV, -1);

        bool found = dfs(x, y);

        if (!found) {
            cout << "-1\n";
            continue;
        }

        // reconstruir caminho
        vector<int> path;
        for (int v = y; v != -1; v = parent[v])
            path.push_back(v);
        reverse(path.begin(), path.end());

        // imprimir contagem (como no enunciado original)
        int count = (path.size() / 2) + 1;
        cout << count << "\n";

        // imprimir vértices (convertendo filmes de volta)
        for (int i = 0; i < (int)path.size(); i++) {
            if (path[i] > OFFSET) cout << path[i] - OFFSET;
            else cout << path[i];
            if (i + 1 < (int)path.size()) cout << " ";
        }
        cout << "\n";
    }
}
