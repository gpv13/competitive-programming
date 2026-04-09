#include<bits/stdc++.h>
using namespace std;

bool get(long long s, long long m, long long limit){

    long long debt = 0;
    for(int i=59;i>=0;i--){
        debt <<= 1;
        if((s >> i) & 1){
            debt += 1;
        }
        if((m >> i) & 1){
            debt -= min(limit, debt);
        }

    }

    return (debt == 0);
}

void solve(){

    long long s, m;
    cin >> s >> m;

    long long l = 0, r = (1LL << 60);
    if(!get(s, m, 1LL << 60)){
        cout << "-1" << endl;
    }
    else{
        long long ans;
        long long mid =(l+r)/2;
        while(l<=r){

            if(get(s, m, mid)){
                ans = mid;
                r = mid-1;
            }else{
                l = mid+1;
            }
            mid = (l+r)/2;
        } 
        cout << ans << endl;
    }

}

int main(){

    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    int t;

    cin >>t;
    while(t--){
        solve();

    }
    return 0;
}