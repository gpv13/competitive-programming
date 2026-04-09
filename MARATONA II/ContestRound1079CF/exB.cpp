#include <bits/stdc++.h>
using namespace std;



void solve() {
    int x;
    cin >> x;
    vector<int> um(x), dois(x);
    for(int i=0;i<x;i++) cin >> um[i];
    for(int i=0;i<x;i++) cin >> dois[i];

    bool deuCerto = true;



    int pos1 = 0, pos2 = 0;

    while(pos2!=x){
        if(pos1 == x) {deuCerto = false; break;}
        if(um[pos1] == dois[pos2]) pos2++;
        else pos1++;
    }

    cout << (deuCerto ? "YES" : "NO") << endl;
}

int main() {
    int t;
    cin >> t;
    while (t--) {
        solve();
    }
    return 0;
}