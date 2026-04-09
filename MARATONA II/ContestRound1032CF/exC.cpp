#include<bits/stdc++.h>
using namespace std;
int main(){

    int t;
    cin >> t;
    for(int k=0;k<t;k++){
        int n, m;
        cin >> n >> m;
        int maior = 0;
        bool certo = false;
        vector<vector<int>> vetor(n, vector<int>(m));
        vector<int> contLinha(n, 0);
        vector<int> contCol(m, 0);
        for(int i=0;i<n;i++){
            for(int j=0; j<m;j++){

                cin >> vetor[i][j];
                if(vetor[i][j] > maior) maior = vetor[i][j];
            }
        }
        int total = 0;
        for(int i=0;i<n;i++){
            for(int j=0;j<m;j++){
                if(vetor[i][j] == maior){
                    contLinha[i]++;
                    contCol[j]++;
                    total++;
                }
            }
        }

        for(int i=0;i<n;i++){
            for(int j=0;j<m;j++){
                int conta = contLinha[i] + contCol[j];
                if(vetor[i][j] == maior){
                    conta--;
                }
                if(total == conta){
                    certo = true;
                    break;
                }
            }
        }
        
        cout << maior - (certo ? 1 : 0) << endl;

    }



    return 0;
}