#include <bits/stdc++.h>
using namespace std;

// Usar variáveis globais para evitar estourar a stack em casos maiores
// e facilitar o tamanho fixo (já que N, M <= 400).
int mat[405][405];
int matPre[405][405];
int N, M, K, Q;

bool check(int time) {
    // Limpa a matriz de prefixos a cada check
    // Usamos índices de 1 até N e 1 até M para facilitar a conta
    for(int i = 1; i <= N; i++){
        for(int j = 1; j <= M; j++){
            // Se a cidade tem dados (!=-1) e o tempo de emergência é <= tempo atual
            int val = (mat[i][j] != -1 && mat[i][j] <= time) ? 1 : 0;
            
            // Soma de prefixos 2D clássica
            matPre[i][j] = val + matPre[i-1][j] + matPre[i][j-1] - matPre[i-1][j-1];
        }
    }

    // Verificar quadrados K x K
    // O quadrado começa em (i, j) e vai até (i+K-1, j+K-1)
    // O limite do loop é N - K + 1
    for(int i = 1; i <= N - K + 1; i++){
        for(int j = 1; j <= M - K + 1; j++){
            int r1 = i, c1 = j;
            int r2 = i + K - 1, c2 = j + K - 1;

            // Soma do sub-retângulo
            int total = matPre[r2][c2] - matPre[r1-1][c2] - matPre[r2][c1-1] + matPre[r1-1][c1-1];

            if(total == K * K) return true;
        }
    }
    return false;
}

int main(){
    ios::sync_with_stdio(false);
    cin.tie(NULL);

    if(!(cin >> N >> M >> K >> Q)) return 0;

    // Inicializa com -1
    for(int i = 0; i <= N; i++){
        for(int j = 0; j <= M; j++){
            mat[i][j] = -1;
        }
    }
    
    for(int i = 0; i < Q; i++){
        int r, c, d;
        cin >> r >> c >> d;
        // O input é 1-based, nossa matriz global também será usada como 1-based
        // Caso haja input duplicado, pega o menor tempo (precaução)
        if(mat[r][c] == -1) mat[r][c] = d;
        else mat[r][c] = min(mat[r][c], d); 
    }

    int ans = -1;
    int l = 1, r = 1000000000; // 10^9 fixo corretamente

    while(l <= r){
        int mid = l + (r - l) / 2;
        
        if(check(mid)){
            ans = mid;    // Guardamos o tempo atual como possível resposta
            r = mid - 1;  // Tenta achar um tempo menor
        } else {
            l = mid + 1;  // Precisa de mais tempo
        }
    }

    cout << ans << endl;

    return 0;
}