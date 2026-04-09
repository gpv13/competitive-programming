#include<bits/stdc++.h>
using namespace std;
#define INF 10000000000

const int MAX = 100;

long long int w[MAX][MAX];

long long d[MAX][MAX];

int n;

void floyd_warshall(){
    for(int i=1; i<=n; i++){
        for(int j=1; j<=n; j++){
            d[i][j] = w[i][j];
        }
    }
    for(int k =1;k<=n;k++){
        for(int i = 1; i<=n; i++){
            for(int j=1; j<=n;j++){
                d[i][j] = min(d[i][j], d[i][k]+d[k][j]);
            }
        }
    }
}

int main(){

    for(int i=0;i<MAX;i++){
        for(int j=0; j<MAX;j++){
            if(i==j){
                w[i][j] = 0;
            }else{
                w[i][j] = INF;
            }
        }
    }
    int m, start, end;
    cin >> n >> m;
    cin >> start >> end;
    for(int i=0; i<m; i++){
        int v1, v2;
        long long int p;
        cin >> v1 >> v2 >> p;
        if(w[v1][v2] == INF){
            w[v1][v2] = p;
        }
        else{
            w[v1][v2] += p;
        }
    }
    floyd_warshall();
    cout << d[start][end] << endl;
}