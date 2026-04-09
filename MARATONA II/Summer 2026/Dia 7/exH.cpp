#include<bits/stdc++.h>
using namespace std;

bool isPossible(const string& s, const string& t, const vector<int>& removidos) {
    int indT = 0;
    for (int i = 0; i < s.size(); i++) {
        if (!removidos[i] && s[i] == t[indT]) {
            indT++;
        }
        if (indT == t.size()) return true;
    }
    return false;
}

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    string s, t;
    cin >> s >> t;

    vector<int> op(s.size());
    for (int i = 0; i < s.size(); i++) {
        cin >> op[i];
        op[i]--; 
    }

    int l = 0, r = s.size() - 1;
    int ans = 0;

    while (l <= r) {
        int mid = l + (r - l) / 2;

        vector<int> removidos(s.size(), 0);
        for (int i = 0; i <= mid; i++) {
            removidos[op[i]] = 1;
        }

        if (isPossible(s, t, removidos)) {
            ans = mid + 1;
            l = mid + 1;
        } else {
            r = mid - 1;
        }
    }

    cout << ans << endl;

    return 0;
}