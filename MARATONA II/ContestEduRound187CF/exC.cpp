#include<bits/stdc++.h>
using namespace std;

long long prox(long long s, long long m){

    int ans;
    long long aux = log2(s);
    for(int i=0;i<aux;i++){
        
    }
}

int main(){

    int t;
    cin >>t;
    while(t--){
        
        long long s, m;
        cin >> s >> m;
        long long conta = 0;
        long long atual = m;
        bool deuRuim = false;
        while(s>0){

            int quant = s/atual;
            conta += quant;
            s-= atual*quant;

            atual = prox(long long s, long long m);

            if(deuRuim)break;
        }    
        if(deuRuim) cout << "-1" << endl;
        else cout << conta << endl;
    }

    return 0;
}