#include<bits/stdc++.h>
using namespace std;
int main(){

    long long int n;
    cin >> n;
    long long int tempoatual = 0;
    vector<long long int> horas, duracao;
    for(long long int i=0;i<n;i++){
        long long int t, d;
        cin >> t >> d;
        horas.push_back(t);
        duracao.push_back(d);
    }
    for(long long int i=0;i<n;i++){
        if(tempoatual<horas[i]){
            tempoatual+= horas[i] - tempoatual;
        }
        tempoatual += duracao[i];
    }
    cout << tempoatual << endl;

    return 0;
}