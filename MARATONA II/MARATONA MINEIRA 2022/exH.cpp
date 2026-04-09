#include<bits/stdc++.h>
using namespace std;

long long int contaBordas(long long int x, long long int y, long long int l, long long int c){

        vector<long long int> dx = {-1, -1, 0, 1, 1, 1, 0, -1};
        vector<long long int> dy = {0, 1, 1, 1, 0, -1, -1, -1};
        long long int bordas = 0;
        for(long long int i=0;i<8;i++){
            if(x+ dx[i] >=0 && x+dx[i] < l && y+dy[i] >=0 && y+dy[i] < c) bordas++;
        }
        return bordas;
}

void brinca(long long int l, long long int c, long long int x, long long int y, vector<vector<long long int>>& mat){
    long long int jogadas = l+c;
    pair<long long int,long long int> pos = {x, y};
    vector<long long int> dx = {0, -1, -1, -1, 0, 1, 1, 1};
    vector<long long int> dy = {-1, -1, 0, 1, 1, 1, 0, -1};
    while(jogadas--){

        long long int bordas = contaBordas(x, y, l, c);
        long long int quant = mat[x][y] - (mat[x][y] % bordas);
        mat[x][y] -= quant;
        for(long long int i=0;i<8;i++){
            if(x+ dx[i] >=0 && x+dx[i] < l && y+dy[i] >=0 && y+dy[i] < c) mat[x+dx[i]][y+dy[i]] += quant/bordas;
        }



        long long int maior = -1;
        pair<long long int, long long int> maiorPos = {-1,-1};
        for(long long int i=0;i<8;i++){
            if(x+ dx[i] >=0 && x+dx[i] < l && y+dy[i] >=0 && y+dy[i] < c && mat[x+dx[i]][y+dy[i]] > maior){ 
                maior = mat[x+dx[i]][y+dy[i]];
                maiorPos = {x+dx[i] , y+dy[i]};
            }
        }

        x = maiorPos.first; y = maiorPos.second; 
    }
}

int main(){

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    long long int l, c;
    cin >> l >> c;
    vector<vector<long long int>> mat(l, vector<long long int>(c));
    for(long long int i=0;i<l;i++){
        for(long long int j=0;j<c;j++){
            cin >> mat[i][j];
        }
    }
    
    long long int x, y;
    cin >> x >> y;
    x--; y--;
    if(l == 1 &&  c == 1){
        cout << mat[0][0] << endl;
        return 0;
    }
    brinca(l, c, x, y, mat);

    long long int maior = -1;
    for(long long int i=0;i<l;i++){
        for(long long int j=0;j<c;j++){
            maior = max(maior, mat[i][j]);
        }
    }

    cout << maior << endl;

    return 0;
}