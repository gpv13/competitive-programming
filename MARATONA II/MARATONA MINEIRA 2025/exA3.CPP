#include <iostream>
#include <vector>
#include <set>
#include <cmath> // Para floor

using namespace std;

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int n;
    cin >> n;

    if (n == 0) {
        cout << endl;
        return 0;
    }

    vector<int> cadeiras(n); // Vetor final de resposta (0-indexed)

    // O set vai guardar os segmentos de cadeiras livres.
    // A chave de ordenação é {-distância, início_do_intervalo}.
    // O valor é {início_do_intervalo, fim_do_intervalo}.
    // Usamos -distância para que o set (que ordena crescentemente) coloque as maiores distâncias primeiro.
    set<pair<pair<int, int>, pair<int, int>>> segmentos;

    // Fã 1 sempre senta na cadeira 1 (índice 0).
    cadeiras[0] = 1;

    // Se houver mais de um fã, o Fã 2 senta na cadeira N (índice n-1).
    if (n > 1) {
        cadeiras[n - 1] = 2;
    }

    // Após os fãs 1 e 2 sentarem, temos um segmento livre de [1, n-2].
    // Só inserimos esse segmento se ele for válido (n > 2).
    if (n > 2) {
        int L = 1;
        int R = n - 2;
        int dist = (R - L) / 2; // Distância do meio até a borda mais próxima
        segmentos.insert({{-dist, L}, {L, R}});
    }

    // Posiciona os fãs de 3 até N
    for (int i = 3; i <= n; ++i) {
        // Pega o melhor segmento (o primeiro do set, graças à nossa chave de ordenação)
        auto it = segmentos.begin();
        int L = it->second.first;
        int R = it->second.second;
        segmentos.erase(it);

        // Calcula a posição no meio do segmento [L, R]
        int pos = L + (R - L) / 2;
        cadeiras[pos] = i;

        // O segmento [L, R] foi quebrado em dois novos segmentos:
        // 1. Segmento da esquerda: [L, pos - 1]
        if (L <= pos - 1) {
            int newL = L;
            int newR = pos - 1;
            int newDist = (newR - newL) / 2;
            segmentos.insert({{-newDist, newL}, {newL, newR}});
        }

        // 2. Segmento da direita: [pos + 1, R]
        if (pos + 1 <= R) {
            int newL = pos + 1;
            int newR = R;
            int newDist = (newR - newL) / 2;
            segmentos.insert({{-newDist, newL}, {newL, newR}});
        }
    }

    // Imprime o resultado final
    for (int i = 0; i < n; ++i) {
        cout << cadeiras[i] << (i == n - 1 ? "" : " ");
    }
    cout << endl;

    return 0;
}