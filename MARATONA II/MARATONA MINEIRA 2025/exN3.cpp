#include<bits/stdc++.h>
using namespace std;

void solve(){

    string s;
    cin >> s;
    int n = s.size();
    vector<char> suffix_array(s.size());
    suffix_array[n-1] = s[n-1];
    for(int i=n-2; i>=0;i--){
        suffix_array[i] = min(suffix_array[i+1], s[i]);
    }
    int posL = -1;
    for(int i=0;i<n;i++){
        if(s[i] > suffix_array[i]){
            posL = i;
            break;
        }
    }
    if(posL!=-1){
        int posR = posL;

        
        for(int i = posL; i <n;i++){
            if(s[i] == suffix_array[posL]) posR = i;
        }

        reverse(s.begin()+posL, s.begin() + posR + 1);
    }
    cout << s << endl;
}

int main(){

    solve();
    return 0;
}