#include<bits/stdc++.h>
using namespace std;

//1 se pode, 0 se foi num impar, -1 se foi par
int isPossible(int x, vector<int>& dists){
    int atual = x;
    for(int i=0;i<dists.size();i++){
        if(atual >= dists[i]){
            return (i % 2) ? 0 : -1;
        }
        atual = dists[i] - atual;
    }
    return 1;
}

int main(){

    int n;
    cin >> n;
    vector<int> dists;
    vector<pair<int,int>> pontos(n);
    for(int i=0;i<n;i++){
        int a, b;
        cin >> a >> b;
        pontos[i] = {a,b};
        if(i) dists.push_back(abs(pontos[i].first - pontos[i-1].first) + abs(pontos[i].second - pontos[i-1].second));
    }
    int l = 1;
    int r = 1e9 + 1;

    int mid = (l+r)/2;
    int ans = -1;
    while(l<=r){
        mid = (l+r)/2;
        int p = isPossible(mid, dists);
        if(p == 1){
            ans = (max(mid, ans));
            l = mid + 1;
        }else if(p == 0){
            l = mid + 1;
        }else{
            r = mid - 1;
        }
    }

    cout << ans << endl;

    return 0;
}