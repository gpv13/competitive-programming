#include <bits/stdc++.h>
using namespace std;

int main() {
    int n;
    while (cin >> n && n != 0) {
        int total_pares = 0;
        for (int i = 0; i < n; i++) {
            int c, v;
            cin >> c >> v;
            total_pares += (v / 2); // só pares importam
        }
        cout << (total_pares / 2) << '\n'; // 2 pares formam 1 retângulo
    }
    return 0;
}
