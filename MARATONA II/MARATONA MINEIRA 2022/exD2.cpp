#include<bits/stdc++.h>
using namespace std;

int main(){

    int n,m, k, q;
    cin >> n >> m >> k >> q;
    int mat[n][m];
    for(int i=0;i<n;i++){
        for(int j=0;j<m;j++){
            mat[i][j] = -1;
        }
    }
    
    for(int i=0;i<q;i++){
        int x, y, v;
        cin >> x >> y >> v;
        x--; y--;
        mat[x][y] = v; 
    }
    int ans = -1;
    int l = 1, r = 1e9 + 7, mid = (l+r)/2; 
    while(l<=r){
        bool deuCerto = false;
        mid = (l+r)/2;
        int matPre[n][m];
        for(int i=0;i<n;i++){
            for(int j=0;j<m;j++){
                if(mat[i][j] != -1 && mat[i][j] <= mid) matPre[i][j] = 1;
                else matPre[i][j] = 0;
            }
        }
        int matPre2D[n][m];
        matPre2D[0][0] = matPre[0][0];
        for(int i=1;i<n;i++)matPre2D[i][0] = matPre2D[i-1][0] + matPre[i][0];
        for(int i=1;i<m;i++)matPre2D[0][i] = matPre2D[0][i-1] + matPre[0][i];
        for(int i=1;i<n;i++){
            for(int j=1;j<m;j++){
                matPre2D[i][j] = matPre[i][j] + matPre2D[i-1][j] + matPre2D[i][j-1] - matPre2D[i-1][j-1];
            }
        }
        for(int i=k-1;i<n;i++){
            for(int j=k-1;j<m;j++){
                int aux = matPre2D[i][j];
                if(i>=k && j>=k) aux = aux + matPre2D[i-k][j-k] - matPre2D[i-k][j] - matPre2D[i][j-k];
                else if(i>=k) aux = aux - matPre2D[i-k][j];
                else if(j>=k) aux = aux - matPre2D[i][j-k];
                if(aux == k*k) {ans = mid; deuCerto = true; break;}
            }
            if(deuCerto) break;
        }

        if(deuCerto) r = mid - 1;
        else l = mid + 1;
    }

    cout << ans << endl;

    return 0;
}