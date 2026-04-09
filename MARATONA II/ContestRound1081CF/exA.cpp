#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){

        int n;
        cin >> n;
        string s;
        cin >> s;
        int conta = 0;
        char c;
        bool cont = false;
        for(int i=0;i<n;i++){
            if(!i){
                conta++;
                c = s[i];
            }else{
                if(s[i] != c){
                    conta++;
                    c = s[i];
                }else{
                    cont = true;
                }
            }
        }
        if(s[0] != s[n-1] && cont) conta++;
        cout << conta << endl;
    }


    return 0;
}