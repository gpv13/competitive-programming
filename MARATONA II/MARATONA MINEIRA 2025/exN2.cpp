#include<bits/stdc++.h>
using namespace std;

int main(){

    string s;
    cin >> s;
    bool letras[26] = {false};
    letras[0] = true;
    bool achou = false;
    pair<char,int> erro = {'z', -1}, fimErro = {'z' + 1, -1};
    for(int i=0;i<s.size();i++){
        if(!letras[s[i]-'a']){
            for(int j=i;j<s.size();j++){
                if(s[j] < s[i]){
                    achou = true;
                    if(erro.second == -1) erro = {s[i], i};
                    if(s[j] <= fimErro.first){
                        fimErro = {s[j], j};
                    }
                }
            }
            letras[s[i] -'a'] = true;
        }   
        if(achou) break;
    }
    string aux;
    for(int i=erro.second;i<=fimErro.second;i++){
        aux+=s[i];
    }
    reverse(aux.begin(),aux.end());
    string res;
    for(int i=0;i<erro.second;i++){
        res+=s[i];
    }
    res+=aux;
    for(int i=fimErro.second+1;i<s.size();i++) res+=s[i];

    cout << res << endl;

    return 0;
}