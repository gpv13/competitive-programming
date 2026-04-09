#include<bits/stdc++.h>
using namespace std;

struct Edge{
    int to;
    int cap;
};
#define INF 100000000
#define MAXN 101

vector<int> g[MAXN];
vector<Edge> edges;

void addEdge(int a, int b, int c){
    g[a].push_back(edges.size());
    edges.push_back({b,c});
    g[b].push_back(edges.size());
    edges.push_back({a, 0}); //edge voltando com cap 0
}

int bfs(int sink, int target, vector<pair<int,int>>& pai){

    fill(pai.begin(),pai.end(), make_pair(-1,-1));

    queue<int> q;
    q.push(sink);
    vector<bool> visited(MAXN, false);
    visited[sink] = true;
    // int flow = INF;

    vector<int> bestFlow(MAXN, 0);
    bestFlow[sink] = INF;

    while(!q.empty()){
        int u = q.front();
        // visited[u] = true;
        q.pop();
        for(auto idx : g[u]){

            int v = edges[idx].to;

            if(!visited[v] && edges[idx].cap > 0) {
                q.push(v);
                visited[v] = true;
                pai[v] = {u, idx};
                // int novoflow = min(flow, edges[v].cap);
                bestFlow[v] = min(bestFlow[u], edges[idx].cap);
                if(v == target){
                    return bestFlow[v];
                }
                // flow = novoflow;
            }
        }

    }
    return 0;
}

int maxFlow(int s, int t){

    vector<pair<int,int>> pai(MAXN, {-1, -1}); //vertice que veio e por qual aresta;
    int flow = 0;
    int aux;
    while(aux = bfs(s, t, pai)){

        flow += aux;
        int curr = t;
        
        while(curr != s){

            int aresta = pai[curr].second;
            edges[aresta].cap -= aux;
            edges[aresta^1].cap += aux;

            curr = pai[curr].first;
        }

    }

    return flow;
}

int main(){

    int n;
    cin >> n;
    int m;
    cin >> m;
    vector<int> originais(m+1, -1);
    for(int i=0;i<m;i++){
        int a, b, c;
        cin >> a >> b >> c;
        a--; b--;
        originais[i] = (edges.size());
        addEdge(a,b,c);
        addEdge(b, a, c);
    }
    cout << maxFlow(0, n-1) << endl;
    for(int i=0;i<m;i++){
        cout << edges[originais[i]^1].cap - edges[(originais[i] + 2) ^ 1].cap << endl;
    }

    return 0;

}