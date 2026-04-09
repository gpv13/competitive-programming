#include <bits/stdc++.h>
using namespace std;

int main() {
    int n;
    cin >> n;
    vector<int> cadeiras(n); // cadeiras[i] = fã que sentou na cadeira i

    // fila de intervalos: {-comprimento, posição inicial, posição final}
    set<tuple<int, int, int>> intervalos;
    intervalos.insert({-n, 0, n - 1});

    for (int fan = 1; fan <= n; fan++) {
        auto [neg_len, l, r] = *intervalos.begin();
        intervalos.erase(intervalos.begin());

        int pos;
        if (fan == 1) {
            pos = 0; // primeiro fã sempre na esquerda
        } else if (fan == 2) {
            pos = n - 1; // segundo fã sempre na direita
        } else {
            pos = (l + r) / 2; // demais fãs sentam no meio
        }

        cadeiras[pos] = fan;

        // atualiza os intervalos livres
        if (l <= pos - 1)
            intervalos.insert({-(pos - l), l, pos - 1});
        if (pos + 1 <= r)
            intervalos.insert({-(r - pos), pos + 1, r});
    }

    // imprime os fãs em ordem das cadeiras
    for (int i = 0; i < n; i++) {
        cout << cadeiras[i] << (i + 1 == n ? '\n' : ' ');
    }

    return 0;
}
