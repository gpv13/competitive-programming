#include <bits/stdc++.h>
using namespace std;

vector<bool> visited;

void dfs(long long v, vector<vector<long long>> const& adj, vector<long long> &output) {
    visited[v] = true;
    for (auto u : adj[v])
        if (!visited[u])
            dfs(u, adj, output);
    output.push_back(v);
}

void strongly_connected_components(vector<vector<long long>> const& adj,
                                   vector<vector<long long>> &components,
                                   vector<vector<long long>> &adj_cond,
                                   vector<long long> &roots) {
    long long n = adj.size();
    components.clear(), adj_cond.clear();

    vector<long long> order;
    visited.assign(n, false);

    for (long long i = 0; i < n; i++)
        if (!visited[i])
            dfs(i, adj, order);

    vector<vector<long long>> adj_rev(n);
    for (long long v = 0; v < n; v++)
        for (long long u : adj[v])
            adj_rev[u].push_back(v);

    visited.assign(n, false);
    reverse(order.begin(), order.end());

    roots.assign(n, -1);

    for (auto v : order)
        if (!visited[v]) {
            vector<long long> component;
            dfs(v, adj_rev, component);
            int comp_id = components.size();
            components.push_back(component);
            for (auto u : component)
                roots[u] = comp_id; // agora roots[v] = id da componente
        }

    adj_cond.assign(components.size(), {});
    for (long long v = 0; v < n; v++)
        for (auto u : adj[v])
            if (roots[v] != roots[u])
                adj_cond[roots[v]].push_back(roots[u]);
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    long long n, m;
    cin >> n >> m;

    vector<vector<long long>> adj(n);

    for (long long i = 0; i < m; i++) {
        long long a, b;
        cin >> a >> b;
        --a; --b;
        adj[a].push_back(b);
    }

    vector<vector<long long>> components, adj_cond;
    vector<long long> roots;
    strongly_connected_components(adj, components, adj_cond, roots);

    long long maxLig = 0;
    for (int i = 0; i < (int)adj_cond.size(); i++) {
        if (adj_cond[i].empty())
            maxLig++;
    }

    cout << maxLig << "\n";
    return 0;
}
