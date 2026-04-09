#include<bits/stdc++.h>
using namespace std;

vector<int> distances;
int queijoMaisProx;

void bfs(int x, int y, vector<string> maze, int n, int m) {

    queue<pair<int,int>> q;
    vector<vector<int>> dists(n, vector<int>(m));
    q.push({x,y});
    dists[x][y] = 0;
    while (!q.empty()) {
        pair<int,int> u = q.front();
        q.pop();
        maze[u.first][u.second] = '#';
        if(u.second>0 && maze[u.first][u.second-1] == '.'){ //cima
            dists[u.first][u.second-1] = dists[u.first][u.second] + 1;
            distances.push_back(dists[u.first][u.second] + 1);
            q.push({u.first,u.second-1});
        }
        if(u.second<m-1 && maze[u.first][u.second+1] == '.'){ //baixo
            dists[u.first][u.second+1] = dists[u.first][u.second] + 1;
            distances.push_back(dists[u.first][u.second] + 1);
            q.push({u.first,u.second+1});
        }
        if(u.first>0 && maze[u.first-1][u.second] == '.'){ //esquerda
            dists[u.first-1][u.second] = dists[u.first][u.second] + 1;
            distances.push_back(dists[u.first][u.second] + 1);
            q.push({u.first-1,u.second});
        }
        if(u.first<n-1 && maze[u.first+1][u.second] == '.'){ //direita
            dists[u.first+1][u.second] = dists[u.first][u.second] + 1;
            distances.push_back(dists[u.first][u.second] + 1);
            q.push({u.first+1,u.second});
        }

        //verificaQueijo

        if(u.second>0 && maze[u.first][u.second-1] == 'Q'){ //cima
            if(queijoMaisProx == -1) queijoMaisProx = dists[u.first][u.second]+1;
        }
        if(u.second<m-1 && maze[u.first][u.second+1] == 'Q'){ //cima
            if(queijoMaisProx == -1) queijoMaisProx = dists[u.first][u.second]+1;
        }
        if(u.first>0 && maze[u.first-1][u.second] == 'Q'){ //cima
            if(queijoMaisProx == -1) queijoMaisProx = dists[u.first][u.second]+1;
        }
        if(u.first<n-1 && maze[u.first+1][u.second] == 'Q'){ //cima
            if(queijoMaisProx == -1) queijoMaisProx = dists[u.first][u.second]+1;
        }
    }
}

int main(){

    int n, m, k;
    pair<int,int> ratPos;
    vector<string> maze(n);
    queijoMaisProx = -1;


    cin >> n >> m >> k;
    for(int i=0;i<n;i++){
        for(int j =0;j<m;j++){
            int aux;
            cin >> aux;
            maze[i] += aux;
            if(aux == 'R') ratPos = {i, j}; 
        }
    }
    bfs(ratPos.first, ratPos.second, maze, n, m);
    sort(distances.begin(), distances.end());
    

    return 0;
}