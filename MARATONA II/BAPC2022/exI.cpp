#include<bits/stdc++.h>

using namespace std;

struct Edge{
    string to;
    double val;
};

// BFS - O(V + E)
unordered_map<string, vector<Edge>> adj;   // lista de adjacência

double bfs(double valor, string origem, string end) {
    queue<string> q;
    unordered_map<string , double> dist;

    q.push(origem);
    dist[origem] = valor;
    bool encontrou = false;
    while (!q.empty()) {
        string u = q.front();
        q.pop();


        if(u == end){
            return dist[u];
        }
        // Processa o vértice u aqui, se necessário

        for (auto v : adj[u]) {


            if (!dist.count(v.to)) {
                    dist[v.to] = dist[u] * v.val;
                    q.push(v.to);
            }

        }
    }
    return -1;
}

int main(){

    int n, q;
    cin >> n >> q;
    for(int i=0;i<n;i++){
        double um, quant;
        char igual;
        string de, para;
        cin >> um >> de >> igual >> quant >> para;
        adj[de].push_back({para, (double)quant});
        adj[para].push_back({de, (double)1/quant});

    }
    cout << setprecision(15); 
    for(int i=0;i<q;i++){

        double valor;
        string de, para, to;

        cin >> valor >> de >> to >> para;
        double res = bfs(valor, de, para);
        if(res == -1) cout << "impossible" << endl;
        else cout << res << endl;

    }


    return 0;
}