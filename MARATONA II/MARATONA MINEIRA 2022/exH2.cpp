#include <bits/stdc++.h>
using namespace std;

int dx[] = {0, -1, -1, -1, 0, 1, 1, 1};
int dy[] = {-1, -1, 0, 1, 1, 1, 0, -1};

void brinca(int l, int c, int x, int y, vector<vector<long long>>& mat) {
    int jogadas = l + c + 1;

    while (jogadas--) {
        long long bordas = 0;
        for (int i = 0; i < 8; i++) {
            int nx = x + dx[i];
            int ny = y + dy[i];
            if (nx >= 0 && nx < l && ny >= 0 && ny < c) {
                bordas++;
            }
        }

        if (bordas > 0) {
            long long atual = mat[x][y];
            long long paraDistribuir = atual - (atual % bordas);
            long long cota = paraDistribuir / bordas;

            if (paraDistribuir > 0) {
                mat[x][y] -= paraDistribuir;
                for (int i = 0; i < 8; i++) {
                    int nx = x + dx[i];
                    int ny = y + dy[i];
                    if (nx >= 0 && nx < l && ny >= 0 && ny < c) {
                        mat[nx][ny] += cota;
                    }
                }
            }
        }


        if (jogadas == 0) break;


        long long maior = -1;
        int proximoX = -1, proximoY = -1;


        for (int i = 0; i < 8; i++) {
            int nx = x + dx[i];
            int ny = y + dy[i];

            if (nx >= 0 && nx < l && ny >= 0 && ny < c) {

                if (mat[nx][ny] > maior) {
                    maior = mat[nx][ny];
                    proximoX = nx;
                    proximoY = ny;
                }
            }
        }


        if (proximoX != -1) {
            x = proximoX;
            y = proximoY;
        }
    }
}

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int l, c;
    if (!(cin >> l >> c)) return 0;

    vector<vector<long long>> mat(l, vector<long long>(c));
    for (int i = 0; i < l; i++) {
        for (int j = 0; j < c; j++) {
            cin >> mat[i][j];
        }
    }

    int x, y;
    cin >> x >> y;
    x--; y--;


    if (l == 1 && c == 1) {
        cout << mat[0][0] << endl;
        return 0;
    }

    brinca(l, c, x, y, mat);

    long long maiorGlobal = -1;
    for (int i = 0; i < l; i++) {
        for (int j = 0; j < c; j++) {
            if (mat[i][j] > maiorGlobal) {
                maiorGlobal = mat[i][j];
            }
        }
    }

    cout << maiorGlobal << endl;

    return 0;
}