#include<bits/stdc++.h>
using namespace std;

long long n; //numero vertices
vector<vector<pair<long long,long long>>> adj; // lista adj
vector<bool> visited, vis2;
vector<long long> tin, low;
long long timer;


map<pair<long long, long long>, long long> bridges;

vector<long long> bloc;//quais blocos estao cada coisa
vector<long long> valorBloc;

void dfsBloc(long long v, long long comp){
    bloc[v] = comp;

    for(auto t : adj[v]){
        long long to = t.first;

        if(bridges.count({v, to}) || bridges.count({to, v})) continue;

        if(bloc[to] == -1){
            dfsBloc(to, comp);
        }
    }
}

void dfsBridges(long long v, long long p = -1) {
    visited[v] = true;
    tin[v] = low[v] = timer++;
    
    for (auto t : adj[v]) {
        long long to = t.first;
        if (to == p) continue; // Ignora a aresta de volta para o pai
        
        if (visited[to]) {
            // Aresta de retorno (back-edge)
            low[v] = min(low[v], tin[to]);
        } else {
            // Aresta da árvore (tree-edge)
            dfsBridges(to, v);
            low[v] = min(low[v], low[to]);
            
            // Condição para ser ponte
            if (low[to] > tin[v]) {
                // Guarda a ponte (garantindo que u < v se quiser ordenar depois)
                bridges.insert({{min(v, to), max(v, to)}, t.second});
            }
        }
    }
}
bool deuRuim;

long long dfsTopDown(long long v, vector<vector<pair<long long,long long>>>& adj2, long long arestaPai){


    vis2[v] = true;
    long long acumAtual = valorBloc[v];
    for(auto u : adj2[v]){
        long long to = u.first;
        long long value = u.second;
        if(!vis2[to]){
            acumAtual += dfsTopDown(to, adj2, value);
        }
    }
    if(arestaPai == -1) return 0;

    if(abs(acumAtual) > arestaPai){
        deuRuim = true;
    }
    return acumAtual;
}

void find_bridges() {
    timer = 0;
    visited.assign(n, false);
    vis2.assign(n,false);
    tin.assign(n, -1);
    low.assign(n, -1);
    bridges.clear();
    
    // Roda a DFS para cada componente conexa
    for (int i = 0; i < n; ++i) {
        if (!visited[i]) {
            dfsBridges(i);
        }
    }
}

int main() {

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    long long t;
    cin >> t;
    while(t--){

        deuRuim = false;
        long long m;
        cin >> n >> m;
        
        bloc.assign(n, -1);
        adj.assign(n, vector<pair<long long,long long>>());
        
        vector<long long> val;
        for(int i=0;i<n;i++){
            long long aux;
            cin >> aux;
            val.push_back(aux);
        }

        for (int i = 0; i < m; ++i) {
            long long u, v, c;
            cin >> u >> v >> c;
            u--; v--; 
            adj[u].push_back({v, c});
            adj[v].push_back({u, c});
        }
        
        find_bridges();
        
        long long sccs = 0;
        for(int i=0;i<n;i++){
            if(bloc[i] == -1) {
                dfsBloc(i, sccs++);
            }
        }

        valorBloc.assign(sccs, 0);

        for(int i=0;i<n;i++){
            valorBloc[bloc[i]] += val[i];
        }

        vector<vector<pair<long long ,long long>>> adj2(sccs, vector<pair<long long,long long>>());

        for(auto b : bridges){
            adj2[bloc[b.first.first]].push_back({bloc[b.first.second], b.second});
            adj2[bloc[b.first.second]].push_back({bloc[b.first.first], b.second});
        }

        dfsTopDown(0, adj2, -1);

        if(deuRuim) cout << "NIE" << endl;
        else cout << "TAK" << endl;

    }       
    return 0;
}