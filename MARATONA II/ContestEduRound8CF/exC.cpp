#include<bits/stdc++.h>
using namespace std;
int main(){

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int n, dist;
    cin >> n >> dist;
    string s;
    cin >> s;
    if(25*n < dist){
        cout << "-1" << endl;
    }else{

        int conta = 0;
        string nova;
        for(int i=0;i<n;i++){
            char c = (abs(s[i] - 'z') < abs(s[i] - 'a')) ? 'a' : 'z';
            int aux = (abs(s[i] - 'z') < abs(s[i] - 'a')) ? abs(s[i] - 'a') : abs(s[i] - 'z');
            if(conta == dist){
                nova+=s[i];
            }
            else if(conta+aux > dist){
                if(c == 'a'){
                    c=s[i] - (dist-conta);
                }else{
                    c= s[i] + (dist-conta);
                }
                nova+=c;
                conta = dist;
            }
            else{
                nova+=c;
                conta += aux;
            }
            // cout << conta << " ";
        }
        if(conta < dist) cout << "-1" << endl;
        else cout << nova << endl;
    }

    return 0;
}