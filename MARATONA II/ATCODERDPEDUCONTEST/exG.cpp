#include<bits/stdc++.h>
using namespace std;
vector<vector<int>> adj(100001);
int dp[112345];

int solve(int v){

    if(dp[v] != -1) return dp[v];

    if(adj[v].empty()) return dp[v] = 1;
    else{
        int valor = 0;
        for(auto u : adj[v]){
            valor = max(solve(u) + 1, valor);
        }
        dp[v] = valor;
        return valor;
    }

}

int main(){

    int n, m;
    cin >> n >> m;
    for(int i=0;i<m;i++){
        int de, para;
        cin >> de >> para;
        de--; para--;
        adj[de].push_back(para);
    }
    memset(dp, -1, sizeof(dp));
    vector<pair<int, int>> menores;
    int maior = 0;
    for(int i=0;i<n;i++){
        maior = max(maior, solve(i));
    }
    cout << maior-1 << endl;

    return 0;
}