#include <iostream>
#include <vector>
#include <string>
#include <algorithm>

using namespace std;

int main() {
    string textoLido, formaCorreta;
    cin >> textoLido >> formaCorreta;

    int n = textoLido.size();
    int m = formaCorreta.size();

    vector<int> anterior(m + 1), atual(m + 1);

    for (int j = 0; j <= m; j++)
        anterior[j] = j;

    for (int i = 1; i <= n; i++) {
        atual[0] = i;
        for (int j = 1; j <= m; j++) {
            if (textoLido[i - 1] == formaCorreta[j - 1]) {
                atual[j] = anterior[j - 1];
            } else {
                atual[j] = min({ 
                    anterior[j - 1] + 1,
                    atual[j - 1] + 1, 
                    anterior[j] + 1
                });
            }
        }
        swap(anterior, atual);
    }

    cout << anterior[m] << endl;

    return 0;
}
