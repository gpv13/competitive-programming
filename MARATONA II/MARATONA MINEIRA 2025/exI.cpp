#include <bits/stdc++.h>
using namespace std;

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    int n;
    cin >> n;

    cout << "L 1" << endl;
    cout.flush();
    int acesas_linha1;
    cin >> acesas_linha1;

    for(int j = 1; j <= n; j++) {
        cout << "C " << j << endl;
        cout.flush();
        int resp;
        cin >> resp;

        cout << "L 1" << endl;
        cout.flush();
        int novas_acesas;
        cin >> novas_acesas;

        if(novas_acesas != acesas_linha1) {
            cout << "C " << j << endl;
            cout.flush();
            cin >> resp;

            acesas_linha1 = (acesas_linha1 == n) ? 0 : n;
        } else {
            acesas_linha1 = novas_acesas;
        }
    }

    for(int i = 1; i <= n; i++) {
        cout << "L " << i << endl;
        cout.flush();
        int acesas_linha_i;
        cin >> acesas_linha_i;

        if(acesas_linha_i == 0) {
            cout << "L " << i << endl;
            cout.flush();
            cin >> acesas_linha_i;
        }
    }

    cout << "FIM" << endl;
    cout.flush();

    return 0;
}