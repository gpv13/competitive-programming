#include <bits/stdc++.h>

using namespace std;
long long int t;
#define piii pair<pair<long long int,long long int>,long long int>
#define pii pair<long long int, long long int>

vector<long long int> dijkstra(long long int origem, vector<vector<piii>>& adj){
    long long int n = adj.size();
    vector<long long int> dist(n, 100000000000);
    priority_queue<pii, vector<pii>, greater<pii>> pq;
    dist[origem] = t;
    pq.push({t, origem});
    while(!pq.empty()){
        long long int d = pq.top().first;
        long long int u = pq.top().second;
        pq.pop();

        if(d > dist[u]) continue;

        for(const auto & [peso, v] : adj[u]){

            auto[aberto, fechado] = peso;

            long long int custo;
            if((dist[u] % (aberto + fechado)) >= aberto) custo = (aberto + fechado) - (dist[u] % (aberto + fechado));
            else custo = 0;

            if(dist[v] > dist[u] + custo){
                dist[v] = dist[u] + custo;
                pq.push({dist[v], v});
            }
        }
    }
    return dist;
}

int main(){

    long long int n, m;
    cin >> n >> m >> t;
    vector<vector<piii>> adj(n+2);    

    for(long long int i=0;i<m;i++){
        long long int x, y, a, f;
        cin >> x >> y >> a >> f;
        adj[x].push_back({{a, f}, y});
        //adj[y].push_back({{a, f}, x});
    }

    vector<long long int> destinos = dijkstra(1, adj);
    
    cout << destinos[n] << endl;

    



return 0;
}