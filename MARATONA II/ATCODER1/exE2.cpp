#include <bits/stdc++.h>
using namespace std;

set<string> x;
set<string> y;

bool comeca_com(const string &palavra, const string &prefixo) {
    return palavra.substr(0, prefixo.size()) == prefixo;
}

void esta() {
    vector<string> para_remover;
    for (const auto &palavra : y) {
        for (const auto &prefixo : x) {
            if (comeca_com(palavra, prefixo)) {
                para_remover.push_back(palavra);
                break;
            }
        }
    }
    for (const auto &p : para_remover) {
        y.erase(p);
    }
}

int main() {
    int q;
    cin >> q;
    while (q--) {
        int tipo;
        string nome;
        cin >> tipo >> nome;
        if (tipo == 1) {
            x.insert(nome);
        } else {
            y.insert(nome);
        }
        esta();
        cout << y.size() << endl;
    }
    return 0;
}
