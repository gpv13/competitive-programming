#include<bits/stdc++.h>
using namespace std;

int val[26];
int qt[(1 << 20) + 1];

int main(){

    int n;
    cin >> n;
    string s;
    cin >> s;


    // int max = (1 << 20) + 1;


    // memset(qt, 0, sizeof(qt));

    int aux = 0;
    for(char c = 'a'; c <= 'z'; c++){
        // cout << "1" << endl;
        if(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y') continue;
        val[c - 'a'] = aux++;
    }
    // cout << "3" << endl;

    qt[0] = 1;
    long long ans = 0;
    int mask = 0;

    for(int i=0;i<n;i++){
        // cout << "2" << endl;
        mask ^= (1 << val[s[i] - 'a']);
        ans += qt[mask];

        for(int j=0;j<20;j++) ans += qt[mask ^ (1 << j)];

        qt[mask]++;         

    }

    cout << ans << endl;
    return 0;

}