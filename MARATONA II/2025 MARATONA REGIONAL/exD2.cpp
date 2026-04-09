#include<bits/stdc++.h>
using namespace std;

#define MAXN (1<<21)
vector<pair<int,int>> id;

bool isValid(int mask){


    int pai[6];
    for(int i=0;i<6;i++)
        pai[i] = -1;

    int par = 0;

    int cnt = 0;
    for(int i=mask;i>0; i -= i&-i){

        int pos = __builtin_ctz(i);
        int u = id[pos].first;

        if(pai[u] == -1){
            pai[u] = u;
            cnt++;
        }

        int v = id[pos].second;

        if(pai[v] == -1){
            pai[v] = v;
            cnt++;
        }  

        par ^= (1 << u) ^ (1 << v);

        u = pai[u];
        v = pai[v]; 
        if(u!=v){
            cnt--;
            for(int j=0;j<6;j++){
                if(pai[j] == v) pai[j] = u;
            }
        }

    }




    return (cnt > 1 || __builtin_popcount(par) > 2) ? false : true;
}



int main(){

    ios::sync_with_stdio(false);
    cin.tie(nullptr);

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
    for(int i=1;i<MAXN;i++){
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