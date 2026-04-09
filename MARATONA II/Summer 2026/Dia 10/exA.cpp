#include<bits/stdc++.h>
using namespace std;


pair<int,int> deuBom(string& s, int tam){
    if (tam == 0) return {0, 0};
    const long long p = 31; // Base menor é mais segura com um módulo
    const long long m = 1e9 + 9;
    long long hash_value = 0;
    long long p_pow = 1;
    
    // Potência p^(tam-1)
    for (int i = 0; i < tam - 1; i++) p_pow = (p_pow * p) % m;

    // Calcula a hash da primeira janela
    for (int i = 0; i < tam; i++) {
        hash_value = (hash_value * p + (s[i] - 'a' + 1)) % m;
    }

    unordered_map<long long, int> dic; // Armazena o índice inicial da primeira vez que o hash apareceu
    dic[hash_value] = 0;

    for (int i = 1; i <= (int)s.size() - tam; i++) {
        // Remove a primeira letra e adiciona a nova
        hash_value = (hash_value - (s[i - 1] - 'a' + 1) * p_pow) % m;
        if (hash_value < 0) hash_value += m; // Garante positivo
        hash_value = (hash_value * p + (s[i + tam - 1] - 'a' + 1)) % m;

        if (dic.count(hash_value)) {
            // Verifica a colisão real aqui para ser seguro (opcional se for fraco)
            return {i, i + tam - 1};
        }
        dic[hash_value] = i;
    }
    return {-1, -1};
}


int main(){

    string s;
    cin >> s;

    int l = 1, r = (s.size()/2) + 1, mid;
    pair<int,int> ans = {-1,-1};
    while(l<r){
        mid = (l+r)/2;
        cout << mid << endl;
        pair<int,int> aux = deuBom(s,mid);
        if(aux.first != -1 && aux.second != -1){
            ans = aux;
            r = mid-1;
        }else{
            l = mid+1;
        }

    }
    for(int i=ans.first;i<=ans.second;i++){
        cout << s[i];
    }cout << endl;

    return 0;
}