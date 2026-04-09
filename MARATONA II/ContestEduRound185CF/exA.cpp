#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<vector<int>> lista(n+1, vector<int>(n+1));
        for(int i=0;i<n+1;i++){
            lista[0][i] = 0;
            lista[i][0] = 0;
        }
        int count = 1;
        for(int i=1;i<n+1;i++){
            for(int j = 1; j<n+1;j++){
                lista[i][j] = count++;
            }
        }
        int maiorVal = 0;
        for(int i=1;i<n+1;i++){
            for(int j = 1; j<n+1;j++){
                if(i<n && j<n) maiorVal = max(maiorVal, lista[i][j] + lista[i-1][j] + lista[i+1][j] + lista[i][j-1] + lista[i][j+1]);
                else if(i<n) maiorVal = max(maiorVal, lista[i][j] + lista[i-1][j] + lista[i+1][j] + lista[i][j-1]);
                else if(j<n) maiorVal = max(maiorVal, lista[i][j] + lista[i-1][j] + lista[i][j-1] + lista[i][j+1]);
                else maiorVal = max(maiorVal, lista[i][j] + lista[i-1][j] + lista[i][j-1]);
            }
        }

        cout << maiorVal << endl;
    }
    return 0;
}