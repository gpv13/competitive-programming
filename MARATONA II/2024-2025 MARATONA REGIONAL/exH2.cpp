#include<bits/stdc++.h>
using namespace std;

long long int converte(string s){
    long long ans = 0;
    int bit = 1 << (s.size()-1);
    for(int i=0;i<s.size();i++){
        ans += bit * ((s[i] == '1') ? 1 : 0);
        bit/=2;
    }
    return ans;
}
long long get_remainder(string s, long long n) {
    long long rem = 0;
    for (char c : s) {
        rem = (rem * 2 + (c - '0')) % n;
    }
    return rem;
}

int main(){

    string m, n;
    cin >> m;
    cin >> n;

    vector<string> todosM, todosN;
    int contaAstM = 0, contaAstN = 0;
    for(int i=0;i<m.size();i++) if(m[i] == '*') contaAstM++;
    for(int i=0;i<n.size();i++) if(n[i] == '*') contaAstN++;

    for(int i=0;i< 1 << contaAstM;i++){
        int conta = contaAstM;
        string aux = m;
        while(conta--){
            *find(aux.begin(), aux.end(), '*') = ((i >> conta) & 1) + '0';
        }
        todosM.push_back(aux);
    }


    for(int i=0;i< 1 << contaAstN;i++){
        int conta = contaAstN;
        string aux = n;
        while(conta--){
            *find(aux.begin(), aux.end(), '*') = ((i >> conta) & 1) + '0';
        }
        todosN.push_back(aux);
    }
    string ans = "";
    // cout << "Tdos M: ";
    // for(auto s : todosM) cout << s << " ";
    // cout << endl;
    // cout << "Tdos N: ";
    // for(auto s : todosN) cout << s << " ";
    // cout << endl;

    for(int i=0;i<todosM.size();i++){
        for(int j=0;j<todosN.size();j++){
            if((get_remainder(todosM[i], converte(todosN[j]))) == 0){
                ans = todosM[i];
                break;
            }
        }
        if(ans!="") break;
    }

    // map<int>
    if(ans == "")cout << "-1" << endl;
    else cout << ans << endl;

    return 0;
}