#include<bits/stdc++.h>
using namespace std;

long long int calculaRange(long long int l, long long int n){
    l++;
    return (n + l) * (n-l + 1);
}


int main(){

    long long int t;
    cin >> t;
    while(t--){
        long long int n;
        cin >> n;
        long long int total = 0;
        vector<long long int> numeros(n), pre(n);
        for(long long int i=0;i<n;i++){
            cin >> numeros[i];
            total+=numeros[i];
            if(i==0) pre[i] = numeros[i];
            else pre[i] = numeros[i] + pre[i-1];
            //cout << pre[i] << " ";
        }
        //cout << endl;

        long long int acumulado = 0;
        long long int pos = -1;
        for(long long int i = numeros.size()-1; i>=0;i--){
            acumulado += numeros[i];
            if(calculaRange(i, n) > acumulado){
                acumulado = calculaRange(i, n);
                pos = i;
            }
        }

        long long int aux = n - 1;

        if(pos!=-1){
            while(aux>=pos){

                if(pre[pos-1] + (pre[n-1] - pre[aux-1] + calculaRange(pos, aux)) > acumulado) acumulado = pre[pos-1] + (pre[n-1] - pre[aux-1] + calculaRange(pos, aux));

                aux--;
            }
        }
        cout << acumulado << endl;
    }


    return 0;
}