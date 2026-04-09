#include<bits/stdc++.h>
using namespace std;

vector<int> bfs(int x, int y, int n, int m, vector<string> grid){
    int dx[] = {1, -1, 0, 0};
    int dy[] = {0, 0, 1, -1};
    queue<pair<int,int>> q;
    vector<int> dot_dists;
    vector<vector<int>> dist(n, vector<int>(m, -1));
    q.push({x,y});
    dist[x][y] = 0;
    dot_dists.push_back(0);
    while (!q.empty()) {
        auto [x, y] = q.front();
        q.pop();

        for (int i = 0; i < 4; i++) {
            int nx = x + dx[i], ny = y + dy[i];
            if (nx >= 0 && nx < n && ny >= 0 && ny < m && grid[nx][ny] != '#' && dist[nx][ny] == -1) {
                dist[nx][ny] = dist[x][y] + 1;
                if (grid[nx][ny] == '.') {
                    dot_dists.push_back(dist[nx][ny]);
                }
                q.push({nx, ny});
            }
        }
    }
    return dot_dists;
}

int gcd(int a, int b) {
    while (b) {
        a %= b;
        int temp = a;
        a = b;
        b = temp;
    }
    return a;
}

void simplifica(int& num, int& den){
    while(gcd(num, den) != 1){
        int aux = gcd(num, den); 
        num/=aux; den/=aux;
    }
}

int main(){

    int n, m, t, x, y;
    cin >> n >> m >> t >> x >> y;
    vector<string> grid (n);
    x--; y--;
    for(int i=0;i<n;i++){
        string aux;
        cin >> aux;
        grid[i] = aux;
    }
    vector<int> dot_dist = bfs(x, y, n, m, grid);
    int contasafe = 0; 
    for(int i=0;i<n;i++){
        for(int j=0;j<m;j++){
            if(grid[i][j] == '.') contasafe++;
        }
    }
    sort(dot_dist.begin(), dot_dist.end());
    int aux = 0;
    int contaDeu = 0;
    while(aux < dot_dist.size() && dot_dist[aux] <= t){
        contaDeu++;
        aux++;
    }

    simplifica(contaDeu, contasafe);
    cout << contaDeu << " " << contasafe << endl;

    return 0;
}