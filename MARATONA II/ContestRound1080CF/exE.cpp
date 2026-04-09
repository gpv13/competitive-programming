#include<bits/stdc++.h>
using namespace std;

#define MOD 1000000007;

long long int solve(vector<long long int>& memo, vector<pair<long long int,long long int>>& adj, long long int pos){

    if(memo[pos] != -1){
        return memo[pos];
    }
    long long int ans;

    ans = 2;
    if(adj[pos].first != 0) ans+= solve(memo, adj, adj[pos].first) % MOD; 
    if(adj[pos].second != 0) ans+= solve(memo, adj, adj[pos].second) % MOD;


    return memo[pos] = ans % MOD;
}

long long int solvePai(vector<long long int>& memoAns, vector<long long int>& memo, vector<long long int>& pai, long long int pos){

    if(memoAns[pos] != -1) return memoAns[pos];
    if(pos == 0) return 1;

    long long int ans = (memo[pos] + solvePai(memoAns, memo, pai, pai[pos])) % MOD;

    return memoAns[pos] = (ans-1)%MOD;

}

int main(){

    long long int t;
    cin >> t;
    while(t--){

        long long int n;
        cin >> n;
        vector<pair<long long int,long long int>> adj(n+1);
        vector<long long int>memo(n+1, -1);
        memo[0] = 1;
        for(long long int i=1;i<=n;i++){
            long long int x, y;
            cin >> x >> y;
            adj[i] = {x,y}; 
        }
        vector<long long int> pai(n+1);
        for(long long int i=1;i<=n;i++){
            if(adj[i].first != 0) pai[adj[i].first] = i;
            if(adj[i].second != 0) pai[adj[i].second] = i;        
        }

        // for(long long int i=1;i<=n;i++) cout << pai[i] << " ";
        // cout << endl;
        
        vector<long long int> memoAns(n+1, -1);
        for(long long int i=1;i<=n;i++){
            if(i!=1) cout << " ";
            cout << (solve(memo, adj, i) - 1 + solvePai(memoAns, memo, pai, pai[i]) - 1) % MOD;
        }
        cout << endl;

        cout << "memo: ";
        for(auto p : memo) cout << p << " ";
        cout << endl << "memoPai: ";
        for(auto p : memoAns) cout << p << " "; 

    }


    return 0;
}