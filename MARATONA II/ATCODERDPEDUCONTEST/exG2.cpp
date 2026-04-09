#include<bits/stdc++.h>
using namespace std;

vector<int> adj[112345];

int main(){


    int n, m;
    cin >> n >> m;

    while(m--){
        int x, y;
        cin >> x >> y;
        adj[x].push_back(y);
    }
    


    return 0;
}