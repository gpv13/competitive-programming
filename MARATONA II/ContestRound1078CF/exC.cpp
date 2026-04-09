#include <bits/stdc++.h>
using namespace std;

string veSeTaBom(int d, int n, int k, const vector<vector<int>>& letras) {
    string res = "";
    for (int i = 0; i < d; i++) {
        char candidato = ' ';
        for (int c = 0; c < 26; c++) {
            bool possivel = true;

            for (int pos = i; pos < n; pos += d) {
                if (letras[pos][c] == 0) {
                    possivel = false;
                    break;
                }
            }
            if (possivel) {
                candidato = (char)('a' + c);
                break;
            }
        }
        
        if (candidato == ' ') return ""; 
        res += candidato;
    }
    
    string final_ans = "";
    while (final_ans.size() < n) final_ans += res;
    return final_ans;
}

void solve() {
    int n, k;
    cin >> n >> k;
    
    vector<vector<int>> letras(n, vector<int>(26, 0));
    for (int i = 0; i < k; i++) {
        string s;
        cin >> s;
        for (int j = 0; j < n; j++) {
            letras[j][s[j] - 'a']++;
        }
    }

    vector<int> divs;
    for (int i = 1; i * i <= n; i++) {
        if (n % i == 0) {
            divs.push_back(i);
            if (i * i != n) divs.push_back(n / i);
        }
    }
    sort(divs.begin(), divs.end());

    for (int d : divs) {
        string ans = veSeTaBom(d, n, k, letras);
        if (ans != "") {
            cout << ans << "\n";
            return;
        }
    }
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    int t;
    cin >> t;
    while (t--) {
        solve();
    }
    return 0;
}