#include<bits/stdc++.h>
using namespace std;
int main(){
    //testar todos os zs
    string s;
    cin >> s;
    pair<char, int> menorLetra = {'z', -1};
    int posComecoInv = -1, posFimInv = -1;
    for(int i = s.size()-1; i>=0;i--){
        if(s[i] < menorLetra.first){
            menorLetra = {s[i], i};
            posFimInv = i;
        }
        else if(s[i] > menorLetra.first){
            posFimInv = i;
        }
    }
    posComecoInv = menorLetra.second;

    string aux, res;
    for(int i=posComecoInv; i>= posFimInv;i--){
        aux+=s[i];
    }
    // cout << aux << endl;
    for(int i=0;i<posFimInv;i++){
        res+=s[i];
    }
    res+=aux;
    for(int i=posComecoInv+1;i<s.size();i++){
        res+=s[i];
    }

    cout << res << endl;

    return 0;
}