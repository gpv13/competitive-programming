#include<bits/stdc++.h>
using namespace std;

//NAO TA CERTO

int main(){

    int t;
    cin >> t;
    while(t--){

        int n, h,k;
        cin >> n >> h >> k;

        vector<long long> tiros(n);
        long long int danoTotalPorMag = 0;
        for(int i=0;i<n;i++){
            cin >> tiros[i];
            danoTotalPorMag += tiros[i];
        }
        vector<long long int> tirosPre(n);
        tirosPre[0] = tiros[0];
        for(int i=1;i<n;i++) tirosPre[i] = tiros[i] + tirosPre[i-1];


        long long quantPentesMin = h/danoTotalPorMag;
        if((danoTotalPorMag*quantPentesMin) == h){
            // cout << "A" << endl;
            cout << (n+k)*quantPentesMin - k << endl;
            continue;
        
        }
        long long tempoMinDessesPentes = (n+k)*quantPentesMin;
        long long tempoDoUltMag = 0;
        long long hpREST = h - (quantPentesMin*danoTotalPorMag);
        long long hpEST2 = hpREST;
        // cout << hpREST << endl;
        
        for(int i=0;i<n;i++){
            tempoDoUltMag++;
            hpREST-=tiros[i];
            if(hpREST<=0) break;
        }

        long long maiorTiroDpsDoMag = -1;
        for(int i=tempoDoUltMag-1;i<n;i++){
            maiorTiroDpsDoMag = max(maiorTiroDpsDoMag, tiros[i]);
        }

        // cout << maiorTiroDpsDoMag << endl;

        long long novoMelhorUltimoTempo = -1;
        for(int i=tempoDoUltMag-1;i>=0;i--){
            // cout << i << " "<< tirosPre[i]<< " " << tiros[i] << endl;
            if(tirosPre[i] - tiros[i] + maiorTiroDpsDoMag >= hpEST2) novoMelhorUltimoTempo = i+1;
        }
        if(novoMelhorUltimoTempo == -1){
            // cout << "B" << endl;
            cout << tempoMinDessesPentes + tempoDoUltMag << endl;
        }else{
            // cout << "C" << endl;
            cout << tempoMinDessesPentes + novoMelhorUltimoTempo << endl;
        }

    }

    return 0;
}