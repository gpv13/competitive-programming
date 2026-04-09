#include<bits/stdc++.h>
using namespace std;

#define GRAPH_MAX_SIZE 1000104
// BFS - O(V + E)
vector<vector<int>> adj(GRAPH_MAX_SIZE);   // lista de adjacência

vector<int> bfs(int start) {
    queue<int> q;
    vector<bool> visited(GRAPH_MAX_SIZE, false);
    vector<int> pai(GRAPH_MAX_SIZE, -1);

    visited[start] = true;
    q.push(start);

    while (!q.empty()) {
        int u = q.front();
        q.pop();

        // Processa o vértice u aqui, se necessário

        for (int v : adj[u]) {
            if (!visited[v]) {
                visited[v] = true;
                pai[v] = u;
                q.push(v);
            }
        }
    }
    return pai;
}

int main(){

    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    int n, m;
    cin >> n >> m;

    for(int i=1;i<=n;i++){
        int num;
        cin >> num;
        for(int j=1;j<=num;j++){
            int aux;
            cin >> aux;
            aux+=101;
            adj[aux].push_back(i);
            adj[i].push_back(aux);
        }
    }
    int q;
    cin >> q;
    for(int i=0;i<q;i++){
        int start, end;
        cin >> start >> end;
        start+=101; end+=101;
        vector<int> pai = bfs(start);
        if(pai[end] == -1){
            cout << "-1" << endl;
        }else{
            vector<int> caminho;
            int auxend = end;
            int cont = 0;
            caminho.push_back(end);
            while(pai[auxend] != -1){
                cont++;
                caminho.push_back(pai[auxend]);
                auxend = pai[auxend];
            }
            cout << (cont/2) + 1 << endl;
            reverse(caminho.begin(), caminho.end());
            bool primeiro = true;
            for(auto nums : caminho){
                if(nums > 101) nums -= 101;
                if(primeiro) cout << nums;
                else cout << " " << nums;
                primeiro = false;
            }
            cout << endl;
        }
    }

    return 0;
}