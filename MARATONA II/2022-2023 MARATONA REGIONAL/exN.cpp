#include<bits/stdc++.h>
using namespace std;
int main(){

    long long int n;
    cin >> n;
    vector<pair<long long int,long long int>> cartas(n);
    for(long long int i=0;i<n;i++){
        cin >> cartas[i].first;
    }
    for(long long int i=0;i<n;i++) cin >> cartas[i].second;
    long long int k, l;
    cin >> k >> l;
    multiset<long long int> sacoVip;
    multiset<long long int, greater<long long int>> sacoReserva;

    long long int somaTotalCima = 0, somaTotal = 0, somaTotalBaixo = 0;
    long long int maiorSoma = -1;


    for(long long int i=n-k;i<n;i++){
        somaTotal += cartas[i].first;
        somaTotalCima += cartas[i].first;
        if(sacoVip.size() < l){
            sacoVip.insert(cartas[i].second);
            somaTotal+=cartas[i].second;
            somaTotalBaixo+=cartas[i].second;
        }else if(*sacoVip.begin() < cartas[i].second){
            long long int valor = *sacoVip.begin();
            sacoReserva.insert(valor);
            somaTotal-=valor;
            somaTotalBaixo-=valor;
            sacoVip.erase(sacoVip.begin());
            sacoVip.insert(cartas[i].second);
            somaTotal+=cartas[i].second;
            somaTotalBaixo+=cartas[i].second;
        }else{
            sacoReserva.insert(cartas[i].second);
        }
    }
    maiorSoma = somaTotal;

    //bota o i, e tira o i+n-k;
    for(long long int i=0;i<k;i++){
        somaTotal-=cartas[i+n-k].first;
        //somtaTotalcIMA
        somaTotal+=cartas[i].first;

        pair<long long int,long long int> cartaASerTirada = cartas[i+n-k], cartaASerBotada = cartas[i];
        if(sacoReserva.count(cartaASerTirada.second)){
            sacoReserva.erase(sacoReserva.find(cartaASerTirada.second));
        }else if(sacoVip.count(cartaASerTirada.second)){
            somaTotal-=cartaASerTirada.second;
            sacoVip.erase(sacoVip.find(cartaASerTirada.second));
        }

        if(cartaASerBotada.second > *sacoVip.begin()){
            somaTotal+=cartaASerBotada.second;
            sacoVip.insert(cartaASerBotada.second);
        }else{
            sacoReserva.insert(cartaASerBotada.second);
        }

        while(sacoVip.size() > l){
            auto it = sacoVip.begin();
            sacoReserva.insert(*it);
            somaTotal-=*it;
            sacoVip.erase(it);
        }
        while(sacoVip.size() < l){
            auto it = sacoReserva.begin();
            sacoVip.insert(*it);
            somaTotal+=*it;
            sacoReserva.erase(it);
        }


        maiorSoma = max(maiorSoma, somaTotal);
    }

    cout << maiorSoma << endl;

    return 0;
}