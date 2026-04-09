#include <iostream>
#include <cmath>
using namespace std;

int main() {
    double erro;
    cin >> erro;

    int termos = 0;
    double proximo;

    do {
        proximo = 1.0 / (2 * termos + 1);
        if (proximo < erro) break;
        termos++;
    } while (true);

    cout << termos+1 << endl;

    return 0;
}
