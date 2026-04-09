#include<bits/stdc++.h>
using namespace std;
#define MOD 1000000000
int soma = 1;
int x, y;
bool final = false;
int solve(char mat[][1001], int startx, int starty){


    if(startx == x-1 && starty == y-1){
        final = true;
        return 0;
    }
    if(mat[startx + 1][starty] == '.' && mat[startx][starty+1] == '.'){
        soma++;
        solve(mat, startx + 1, starty);
        solve(mat, startx, starty + 1);
    }else if(mat[startx + 1][starty] == '.'){
        solve(mat, startx + 1, starty);
    }else if(mat[startx][starty+1] == '.'){
        solve(mat, startx, starty + 1);
    }

    return 0;
}

int main(){

    char mat[1001][1001];
    cin >> x >> y;
    for(int i=0;i<x;i++){
        for(int j=0;j<y;j++){
            cin >> mat[i][j];
        }
    }
    solve(mat, 0, 0);
    if(!final){
        cout << "0" << endl;
    }else{
        cout << (soma%(MOD + 7)) << endl;
    }

    return 0;
}