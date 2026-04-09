#include<bits/stdc++.h>
using namespace std;



int main(){

    int l, c;
    cin >> l >> c;
    vector<string> mat(l);
    for(int i=0;i<l;i++) cin >> mat[i];

    int n;
    cin >> n;
    vector<string> dic(n);
    for(int i=0;i<n;i++){ cin >> dic[i]; cout << dic[i].size() << endl;}

    

    int special[l][c][n];
    memset(special, 0, sizeof(special));

    for(int i=0;i<n;i++){
        cout << "1"<< endl;
        vector<int> letras(26, 0);
        int quantZeros = 26;
        int tam = dic[i].length();
        for(int j =0;j< dic[i].size(); j++){
            if(letras[dic[i][j] - 'A'] == 0) quantZeros--;
            letras[dic[i][j] - 'A']++;
        }
        cout << "comeco hor" << endl;
        //horizontal
        for(int y=0;y<l;y++){
            vector<int> auxLetras = letras;
            int auxQuantZeros = quantZeros; 
            for(int x = 0; x < c;x++){
                cout << x << " " << y << endl;
                if(auxLetras[mat[y][x] - 'A'] == 0) auxQuantZeros--;
                if(--auxLetras[mat[y][x] - 'A'] == 0) auxQuantZeros++;
                if(x >= dic[i].size()){
                    if(auxLetras[mat[y][x - dic[i].size()] - 'A'] == 0) auxQuantZeros--;
                    if(++auxLetras[mat[y][x - dic[i].size()] - 'A'] == 0) auxQuantZeros++;
                }
                if(auxQuantZeros == 26){
                    cout << "Auxquant zer" << endl;
                    for(int k = x; k>=max(0,(int)(x-dic[i].size()));k--){
                        cout << "." << endl; 
                        special[y][k][n]++;
                    }
                    cout << endl;
                }
            }
        }
        cout << "comeco vert"<< endl;
        //vertical
        for(int x=0;x<c;x++){
            vector<int> auxLetras = letras;
            int auxQuantZeros = quantZeros; 
            for(int y = 0; y < l;y++){
                cout << x << " " << y << endl;
                if(auxLetras[mat[y][x] - 'A'] == 0) auxQuantZeros--;
                if(--auxLetras[mat[y][x] - 'A'] == 0) auxQuantZeros++;
                if(y >= dic[i].size()){
                    if(auxLetras[mat[y - dic[i].size()][x] - 'A'] == 0) auxQuantZeros--;
                    if(++auxLetras[mat[y - dic[i].size()][x] - 'A'] == 0) auxQuantZeros++;
                }
                if(auxQuantZeros == 26){
                    cout << "Auxquant zer" << endl;

                    for(int k = y; k>=max((int)(y-dic[i].size()), 0);k--){
                        cout << "." << endl;
                        special[k][x][n]++;
                    }
                }
            }
        }
        cout << "comeco diag dir"<< endl;
        //diagonal direita
        for(int x=0;x<c /*- dic[i].size()*/;x++){
            vector<int> auxLetras = letras;
            int auxQuantZeros = quantZeros; 
            for(int y = 0; y < l /*- dic[i].size()*/;y++){
                if(x!=0 && y!=0) continue;
                cout << x << " " << y << endl;
                int auxX = x, auxY = y, conta = 0;
                while(auxX < c && auxY < l){

                    cout << "auxX y" << auxX << " " << auxY << endl;
                    if(auxLetras[mat[auxY][auxX] - 'A'] == 0) auxQuantZeros--;
                    if(--auxLetras[mat[auxY][auxX] - 'A'] == 0) auxQuantZeros++;
                    if(conta >= dic[i].size() - x && conta>= dic[i].size() - y){
                        if(auxLetras[mat[auxY - dic[i].size()][auxX - dic[i].size()] - 'A'] == 0) auxQuantZeros--;
                        if(++auxLetras[mat[auxY - dic[i].size()][auxX- dic[i].size()] - 'A'] == 0) auxQuantZeros++;
                    }
                    if(auxQuantZeros == 26){
                        cout << "Auxquant zer" << endl;

                        for(int k = conta; k>=max(0,(int)(conta-dic[i].size()));k--){
                            cout << "." << endl;
                            special[y+k][x+k][n]++;
                        }
                    }
                    auxX++; auxY++;
                    conta++;
                }
            }
        }
        cout << "comeco diag esq" << endl;
        for(int x= 0;x<c;x++){
            vector<int> auxLetras = letras;
            int auxQuantZeros = quantZeros; 
            for(int y = 0; y < l /*- dic[i].size()*/;y++){
                if(x!=c-1 && y!=0) continue;
                cout << x << " " << y << endl;
                int auxX = x, auxY = y, conta = 0;
                while(auxX >= 0 && auxY < l){

                    cout << "auxX y" << auxX << " " << auxY << endl;
                    
                    if(auxLetras[mat[auxY][auxX] - 'A'] == 0) auxQuantZeros--;
                    if(--auxLetras[mat[auxY][auxX] - 'A'] == 0) auxQuantZeros++;
                    if(conta >= dic[i].size() - x && conta>= dic[i].size() - y){
                        if(auxLetras[mat[auxY - dic[i].size()][auxX- dic[i].size()] - 'A'] == 0) auxQuantZeros--;
                        if(++auxLetras[mat[auxY - dic[i].size()][auxX- dic[i].size()] - 'A'] == 0) auxQuantZeros++;
                    }
                    if(auxQuantZeros == 26){
                        cout << "Auxquant zer" << endl;
                        
                        for(int k = conta; k>=max(0,(int)(conta-dic[i].size()));k--){
                            cout << "." << endl;
                            special[auxY-k][auxX+k][n]++;
                        }
                    }
                    auxX--; auxY++;
                    conta++;
                }
            }
        }
        cout << "fim do n" << endl;
    }
    int conta = 0;
    for(int i=0;i<l;i++){
        for(int j=0;j<c;j++){
            int flag = 0;
            for(int k=0;k<n;k++){
                
                cout << special[j][i][k] << " ";

                if(special[j][i][k] != 0){
                    flag++;
                }else cout << "uau" << endl; 
            }
            cout << endl;
            if(flag > 1) {conta++; cout << i << " " << j << endl;}
        }
    }

    cout << conta << endl;

    return 0;
}