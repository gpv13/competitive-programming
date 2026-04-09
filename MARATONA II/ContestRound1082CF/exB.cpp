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

        if(n%2){
            bool deuRuim = false;

            if(s[0] == 'b') deuRuim = true;
            else{
                for(int i=1;i<n;i++){
                    if(!(i%2)){
                        if(s[i] == s[i-1]){
                            if(s[i] == '?' && s[i-1] == '?');
                            else{
                                deuRuim = true;
                                break;
                            }
                        }
                    }
                }
            }
            if(deuRuim) cout << "NO";
            else cout << "YES";
            cout << endl;
        }else{
            bool deuRuim = false;
            for(int i=0;i<n;i++){
                if(i%2){
                    if(s[i] == s[i-1]){
                        if(s[i] == '?' && s[i-1] == '?');
                        else{
                            deuRuim = true;
                            break;
                        }
                    }
                }
            }
            if(deuRuim) cout << "NO";
            else cout << "YES";
            cout << endl;
        }

    }


    return 0;
}