#include<bits/stdc++.h>
using namespace std;

#define MAXN (1<<21)
vector<pair<int,int>> id;

void dfs(int s, vector<bool>& vis, const vector<int> adj[]){
    int v = s;
    vis[v] = true;
    for(auto u : adj[v]){
        if(!vis[u]){
            dfs(u, vis, adj);
        }
    }
}

bool isValid(int mask){

    vector<int> adj[6];
    for(int i=mask;i>0; i -= i&-i){
        // cout << "oi" << endl;
        int pos = __builtin_ctz(i);
        int u = id[pos].first;
        int v = id[pos].second;
        adj[u].push_back(v);
        adj[v].push_back(u);
    }
    // cout << "tchau\n";
    vector<bool> vis(6, false);
    dfs(0, vis, adj);
    int contaImp = 0;
    for(int i=0;i<6;i++){
        if(!vis[i]) return false;
        if(adj[i].size() % 2) contaImp++;
        if(contaImp > 2) return false;
    }



    return true;
}



int main(){

    int t;
    cin >> t;

    int d[6][6];

    for(int i=0;i<6;i++){
        for(int j=i;j<6;j++){
            d[i][j] = id.size();
            id.push_back({i,j});
        }
    }

    vector<int> A(MAXN, 0);
    for(int i=0;i<MAXN;i++){
        if(isValid(i)){
            A[i]++;
        }
    }

    vector<int> F(MAXN);
    for (int i = 0; i < MAXN; ++i)
        F[i] = A[i];
    for (int i = 0; i < 21; ++i)
        for (int mask = 0; mask < MAXN; ++mask)
        {
            if (mask & (1 << i))
                F[mask] += F[mask ^ (1 << i)];
        }



    while(t--){

        int n;
        cin >> n;
        int ans = 0;
        for(int i=0;i<n;i++){
            int a, b;
            cin >> a >> b;
            a--; b--;

            int aux = d[a][b];
            ans |= (1<<aux);
        }
        cout << F[ans] << endl;

    }



    return 0;
}