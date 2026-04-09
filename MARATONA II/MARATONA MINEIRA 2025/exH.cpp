#include<bits/stdc++.h>
using namespace std;

bool falhou(vector<int> vetor){
        for(int i=0;i<vetor.size();i++){
            if(i%2 != 0){
                if(vetor[i] < vetor[i-1]) return true;
            } 
        }
        return false;
}

int main(){

    int n;
    cin >> n;
    int num = pow(2, n);
    vector<vector<int>> rodadas(n+1);
    vector<int> pos;
    bool deuErrado = false;
    for(int i=0;i<num;i++){
        int aux;
        cin >> aux;
        if(!i && aux != 0) deuErrado = true;
        pos.push_back(aux);
    }
    if(deuErrado) cout << "-1" << endl;
    else{

        rodadas[0].push_back(1);
        int mult = 1;
        int numerorod = n;
        for(int i=1;i<=n;i++){
            int ind = 1;
            vector<int> ord = rodadas[i-1];
            sort(ord.begin(), ord.end());
            for(int j=0;j<mult;j++){
                while(pos[ind] != numerorod) ind++;
                // rodadas[i].push_back(rodadas[i-1][j]);
                // // cout << rodadas[i-1][j];
                // // cout << " " << ind + 1 << " " << i;
                // // cout << endl;
                // rodadas[i].push_back(++ind);
                int time_vencedor = rodadas[i-1][j];
                int time_oponente = ++ind;

                if (time_vencedor > time_oponente) {
                    deuErrado = true;
                }
                rodadas[i].push_back(time_vencedor);
                rodadas[i].push_back(time_oponente);
            }
            //if(falhou(rodadas[i])) deuErrado = true; 
            if(deuErrado) break;
            mult*=2;
            numerorod--;
        }
        bool primeiro = true;
        
        // for(int i=0;i<num;i++){
        //     if(i%2 != 0){
        //         if(rodadas[n][i] < rodadas[n][i-1]) deuErrado = true;
        //     } 
        // }
        if(deuErrado) cout << "-1" << endl;
        else{
            for(auto numero : rodadas[n]){

                if(primeiro) cout << numero;
                else cout << " " << numero;
                primeiro = false;
            }
            cout << endl;
        }
    }


    return 0;
} 