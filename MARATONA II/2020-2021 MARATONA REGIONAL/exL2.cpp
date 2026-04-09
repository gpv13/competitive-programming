#include<bits/stdc++.h>
using namespace std;

int main(){

    int linhas, colunas;
    cin >> linhas >> colunas;
    vector<string> mat(linhas);
    for(int i=0;i<linhas;i++) cin >> mat[i];

    int n;
    cin >> n;
    vector<string> pal(n);
    for(int i=0;i<n;i++) cin >> pal[i];

    int special[linhas][colunas];
    memset(special, -1, sizeof(special));
    //-1 nao comecou idx encontrou uma vz -2 saturou
    int conta = 0;
    for(int i=0;i<n;i++){
        int tam = pal[i].size();
        // horizontal
        for(int l = 0; l < linhas; l++){
            vector<int> letras(26, 0);
            int zeros = 0;
            for(auto c: pal[i]){
                letras[c-'A']++;
                if(letras[c-'A']==1)
                    zeros++;
            }

            for(int c = 0; c < colunas; c++){
                letras[mat[l][c]-'A']--;
                if(letras[mat[l][c]-'A'] == 0)
                    zeros--;
                if(letras[mat[l][c]-'A'] == -1)
                    zeros++;
                if(c >= tam){
                    letras[mat[l][c-tam]-'A']++;
                    if(letras[mat[l][c-tam]-'A'] == 0)
                        zeros--;
                    if(letras[mat[l][c-tam]-'A'] == 1)
                        zeros++;
                }
                if(zeros==0)
                for(int k = c; k > c-tam; k--)
                {
                    if(special[l][k] == -1)
                    {
                        special[l][k] = i;
                    }
                    else if(special[l][k] != -2 && special[l][k] != i){
                        special[l][k] = -2;
                        conta++;
                    }
                }
            }
        }
        // vertical
        for(int c = 0; c < colunas; c++){
            vector<int> letras(26, 0);
            int zeros = 0;
            for(auto cc: pal[i]){
                letras[cc-'A']++;
                if(letras[cc-'A']==1)
                    zeros++;
            }

            for(int l = 0; l < linhas; l++){
                letras[mat[l][c]-'A']--;
                if(letras[mat[l][c]-'A'] == 0)
                    zeros--;
                if(letras[mat[l][c]-'A'] == -1)
                    zeros++;
                if(l >= tam){
                    letras[mat[l-tam][c]-'A']++;
                    if(letras[mat[l-tam][c]-'A'] == 0)
                        zeros--;
                    if(letras[mat[l-tam][c]-'A'] == 1)
                        zeros++;
                }
                if(zeros==0)
                for(int k = l; k > l-tam; k--)
                {
                    if(special[k][c] == -1)
                    {
                        special[k][c] = i;
                    }
                    else if(special[k][c] != -2 && special[k][c] != i){
                        special[k][c] = -2;
                        conta++;
                    }
                }
            }
        }

        // diagonal direita
        for(int l = 0;l<linhas;l++){
            vector<int> letras(26, 0);
            int zeros = 0;
            for(auto cc: pal[i]){
                letras[cc-'A']++;
                if(letras[cc-'A']==1)
                    zeros++;
            }
            int auxL = l, auxC = 0; 
            while(auxL < linhas && auxC < colunas){
                letras[mat[auxL][auxC]-'A']--;
                if(letras[mat[auxL][auxC]-'A'] == 0)
                    zeros--;
                if(letras[mat[auxL][auxC]-'A'] == -1)
                    zeros++;
                if(auxC >= tam){
                    letras[mat[auxL-tam][auxC-tam]-'A']++;
                    if(letras[mat[auxL-tam][auxC-tam]-'A'] == 0)
                        zeros--;
                    if(letras[mat[auxL-tam][auxC-tam]-'A'] == 1)
                        zeros++;
                }
                if(zeros==0)
                for(int k = 0; k < tam; k++)
                {
                    if(special[auxL-k][auxC-k] == -1)
                    {
                        special[auxL-k][auxC-k] = i;
                    }
                    else if(special[auxL-k][auxC-k] != -2 && special[auxL-k][auxC-k] != i){
                        special[auxL-k][auxC-k] = -2;
                        conta++;
                    }
                }



                auxC++; auxL++;
            }
        }
        for(int c = 0;c<colunas;c++){
            vector<int> letras(26, 0);
            int zeros = 0;
            for(auto cc: pal[i]){
                letras[cc-'A']++;
                if(letras[cc-'A']==1)
                    zeros++;
            }
            int auxL = 0, auxC = c; 
            while(auxL < linhas && auxC < colunas){
                letras[mat[auxL][auxC]-'A']--;
                if(letras[mat[auxL][auxC]-'A'] == 0)
                    zeros--;
                if(letras[mat[auxL][auxC]-'A'] == -1)
                    zeros++;
                if(auxL >= tam){
                    letras[mat[auxL-tam][auxC-tam]-'A']++;
                    if(letras[mat[auxL-tam][auxC-tam]-'A'] == 0)
                        zeros--;
                    if(letras[mat[auxL-tam][auxC-tam]-'A'] == 1)
                        zeros++;
                }
                if(zeros==0)
                for(int k = 0; k < tam; k++)
                {
                    if(special[auxL-k][auxC-k] == -1)
                    {
                        special[auxL-k][auxC-k] = i;
                    }
                    else if(special[auxL-k][auxC-k] != -2 && special[auxL-k][auxC-k] != i){
                        special[auxL-k][auxC-k] = -2;
                        conta++;
                    }
                }



                auxC++; auxL++;
            }
        }
        //diagonal esq
        for(int l = 0;l<linhas;l++){
            vector<int> letras(26, 0);
            int zeros = 0;
            for(auto cc: pal[i]){
                letras[cc-'A']++;
                if(letras[cc-'A']==1)
                    zeros++;
            }
            int auxL = l, auxC = colunas-1; 
            while(auxL < linhas && auxC >= 0){
                letras[mat[auxL][auxC]-'A']--;
                if(letras[mat[auxL][auxC]-'A'] == 0)
                    zeros--;
                if(letras[mat[auxL][auxC]-'A'] == -1)
                    zeros++;
                if(auxC < colunas - tam){
                    letras[mat[auxL-tam][auxC+tam]-'A']++;
                    if(letras[mat[auxL-tam][auxC+tam]-'A'] == 0)
                        zeros--;
                    if(letras[mat[auxL-tam][auxC+tam]-'A'] == 1)
                        zeros++;
                }
                if(zeros==0)
                for(int k = 0; k < tam; k++)
                {
                    if(special[auxL-k][auxC+k] == -1)
                    {
                        special[auxL-k][auxC+k] = i;
                    }
                    else if(special[auxL-k][auxC+k] != -2 && special[auxL-k][auxC+k] != i){
                        special[auxL-k][auxC+k] = -2;
                        conta++;
                    }
                }



                auxC--; auxL++;
            }
        }
        for(int c = 0;c<colunas;c++){
            vector<int> letras(26, 0);
            int zeros = 0;
            for(auto cc: pal[i]){
                letras[cc-'A']++;
                if(letras[cc-'A']==1)
                    zeros++;
            }
            int auxL = 0, auxC = c; 
            while(auxL < linhas && auxC >= 0){
                letras[mat[auxL][auxC]-'A']--;
                if(letras[mat[auxL][auxC]-'A'] == 0)
                    zeros--;
                if(letras[mat[auxL][auxC]-'A'] == -1)
                    zeros++;
                if(auxL >= tam){
                    letras[mat[auxL-tam][auxC+tam]-'A']++;
                    if(letras[mat[auxL-tam][auxC+tam]-'A'] == 0)
                        zeros--;
                    if(letras[mat[auxL-tam][auxC+tam]-'A'] == 1)
                        zeros++;
                }
                if(zeros==0)
                for(int k = 0; k < tam; k++)
                {
                    if(special[auxL-k][auxC+k] == -1)
                    {
                        special[auxL-k][auxC+k] = i;
                    }
                    else if(special[auxL-k][auxC+k] != -2 && special[auxL-k][auxC+k] != i){
                        special[auxL-k][auxC+k] = -2;
                        conta++;
                    }
                }



                auxC--; auxL++;
            }
        }
    }

    cout << conta << endl;

    return 0;
}