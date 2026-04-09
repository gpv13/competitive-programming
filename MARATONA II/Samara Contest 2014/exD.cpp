#include <bits/stdc++.h>
using namespace std;

struct Node {
    int x, y, d;
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    int n, m, v;
    cin >> n >> m >> v;
    int x0, y0, x1, y1;
    cin >> x0 >> y0 >> x1 >> y1;
    x0--, y0--, x1--, y1--; // zero-based

    vector<string> grid(n);
    for (int i = 0; i < n; i++) cin >> grid[i];

    // BFS normal no grid, mas com "passos noturnos" até v
    vector<vector<int>> dist(n, vector<int>(m, -1));
    queue<pair<int,int>> q;

    // podemos começar em qualquer célula, mesmo '.' (pois a primeira fase é noite)
    dist[x0][y0] = 0;
    q.push({x0,y0});

    int dx[4] = {1,-1,0,0};
    int dy[4] = {0,0,1,-1};

    while (!q.empty()) {
        auto [x,y] = q.front(); q.pop();

        // já chegamos?
        if (x == x1 && y == y1) {
            cout << "Hello, Deimos!\n";
            return 0;
        }

        // só podemos "avançar para a próxima noite" a partir de uma floresta
        if (grid[x][y] != 'F' && !(x==x1 && y==y1)) continue;

        // do ponto atual, expandir até v passos durante uma noite
        queue<Node> nq;
        vector<vector<int>> seen(n, vector<int>(m, 0));
        nq.push({x,y,0});
        seen[x][y] = 1;

        while (!nq.empty()) {
            auto [i,j,d] = nq.front(); nq.pop();

            // se chegamos num destino válido (floresta ou a saída)
            if (dist[i][j] == -1) {
                dist[i][j] = dist[x][y] + 1;
                q.push({i,j});
            }

            if (d == v) continue; // limite de passos da noite

            for (int k=0;k<4;k++) {
                int ni=i+dx[k], nj=j+dy[k];
                if (ni<0||nj<0||ni>=n||nj>=m) continue;
                if (seen[ni][nj]) continue;
                seen[ni][nj] = 1;
                nq.push({ni,nj,d+1});
            }
        }
    }

    cout << "Dire victory\n";
}
