#include<bits/stdc++.h>
using namespace std;

struct Edge{
    long long to;
    long long cap;
};
#define INF 1000000000000
#define MAXN 101

vector<long long> g[MAXN];
vector<Edge> edges;

void addEdge(long long a, long long b, long long c){
    g[a].push_back(edges.size());
    edges.push_back({b,c});
    g[b].push_back(edges.size());
    edges.push_back({a, c}); //edge voltando com cap 0
}

long long bfs(long long sink, long long target, vector<pair<long long,long long>>& pai){

    fill(pai.begin(),pai.end(), make_pair(-1,-1));

    queue<long long> q;
    q.push(sink);
    vector<bool> visited(MAXN, false);
    visited[sink] = true;
    // long long flow = INF;

    vector<long long> bestFlow(MAXN, 0);
    bestFlow[sink] = INF;

    while(!q.empty()){
        long long u = q.front();
        // visited[u] = true;
        q.pop();
        for(auto idx : g[u]){

            long long v = edges[idx].to;

            if(!visited[v] && edges[idx].cap > 0) {
                q.push(v);
                visited[v] = true;
                pai[v] = {u, idx};
                // long long novoflow = min(flow, edges[v].cap);
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

vector<long long> bfsResidual(long long s){

    queue<long long> q;
    q.push(s);
    vector<long long> ans;
    vector<bool> visited(MAXN, false);
    ans.push_back(s);
    visited[s] = true;

    while(!q.empty()){

        long long u = q.front();
        q.pop();

        for(auto idx : g[u]){

            long long v = edges[idx].to;
            if(!visited[v] && edges[idx].cap){

                ans.push_back(v);
                visited[v] = true;
                q.push(v);
            }

        }

    }
    return ans;
}

long long maxFlow(long long s, long long t){

    vector<pair<long long,long long>> pai(MAXN, {-1, -1}); //vertice que veio e por qual aresta;
    long long flow = 0;
    long long aux;
    while(aux = bfs(s, t, pai)){

        flow += aux;
        long long curr = t;
        
        while(curr != s){

            long long aresta = pai[curr].second;
            edges[aresta].cap -= aux;
            edges[aresta^1].cap += aux;

            curr = pai[curr].first;
        }

    }

    return flow;
}

vector<long long> minCut( long long s, long long t){

    vector<long long> visitados = bfsResidual(s);
    return visitados;
}


int main(){

    long long n;
    cin >> n;
    long long m;
    cin >> m;
    vector<long long> originais(m+1, -1);
    for(long long i=0;i<m;i++){
        long long a, b, c;
        cin >> a >> b >> c;
        a--; b--;
        // originais[i] = (edges.size());
        addEdge(a,b,c);
        // addEdge(b, a, c);
    }
    long long flow = maxFlow(0, n-1);
    vector<long long> visitados = minCut(0, n-1);
    vector<bool> reach(MAXN, false);
    for(auto u : visitados){
        // cout << u << " ";
        reach[u] = true;
    }
    
    vector<long long> arestas;
    for(auto u : visitados){
        for(auto v : g[u]){
            if(!reach[edges[v].to]){
                arestas.push_back(((v)/2));
                // visited[edges[v].to] = true;
            }
        }
    }
    cout << arestas.size() << " " << flow << endl;
    for(long long i=0;i<arestas.size();i++){
        if(!i) cout << arestas[i] + 1;
        else cout << " " << arestas[i] + 1;
    }cout << endl;

    return 0;

}