#include <bits/stdc++.h>
using namespace std;

//A FAZER FAZER
//FAZER

void solve() {
    int n, m;
    cin >> n >> m;
    int conta = 0;
    int ans;
    vector<vector<int>> mat(n, vector<int>(m));
    vector<int> col(n,0);
    for(int i=0;i<n;i++){
        for(int j=0;j<m;j++){
            cin >> mat[i][j];
            if(mat[i][j]) {conta++; col[i]++;}
        }
    }
    ans = (conta/2) * (conta - conta/2);
    cout << ans << endl;
    int instruct = n+m;
    int total = 0;
    while(instruct--){
        if(total)
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    int t;
    cin >> t;
    while (t--) {
        solve();
    }
    return 0;
}