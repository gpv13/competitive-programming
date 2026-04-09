#include<bits/stdc++.h>
using namespace std;
#define MOD 1000000007

long long pot2[100001];    
long long freq[1000001] = {0};
long long spf[1000001] = {0};
long long count_ocorrunces[1000001] = {0};


int main(){

    int n;
    cin >> n;

    pot2[0] = 1;
    for(int i=1;i<n+1;i++){
        pot2[i] = (pot2[i-1]*2)%MOD;
    }


    for(int i=0;i<n;i++){
        int receita;
        cin >> receita;
        freq[receita]++;
    }

    for(int i=1;i<1000001;i++){
        for(int j = i; j<1000001; j+=i){
            count_ocorrunces[i] += freq[j];
        }
    }

    for(int i=2;i<=1000000;i++){
        if(spf[i] == 0){ //ainda eh primo
            for(int j=i;j<=1000000;j+=i){
                if(spf[j] == 0) spf[j] = i;
            }
        }
    }

    int q;
    cin >> q;
    while(q--){
        int aler;
        cin >> aler;
        vector<int> primos;
        int aux = aler;
        while(aux>1){
            int primo = spf[aux];
            primos.push_back(primo);
            while(aux%primo==0) aux/=primo;
        }
        int total = n;
        int tam = primos.size();
        for(int i=1;i< (1 << tam);i++){

            int mult = 1;
            for(int j=0;j<tam;j++){
                if((i >> j) & 1) mult*=primos[j];
            }
            if(mult!=1){

                if(__builtin_popcount(i) % 2){
                    total -= count_ocorrunces[mult];
                }else{
                    total += count_ocorrunces[mult];
                }

            }
        }
        cout << pot2[total] << endl;
    }


    return 0;
}