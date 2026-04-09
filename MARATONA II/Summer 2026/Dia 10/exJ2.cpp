#include <bits/stdc++.h>
using namespace std;

int main() {

    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    
    long long n, m, l;
    if (!(cin >> n >> m >> l)) return 0;

    map<long long, int> events; 
    for(int i = 0; i < n; i++) {
        long long x, y;
        cin >> x >> y;
        if(y <= l) { 
            long long dist = l - y;
            events[x - dist]++;      
            events[x + dist + 1]--;  
        }
    }

    
    long long soma = 0;
    for(auto it = events.begin(); it != events.end(); ++it) {
        soma += it->second;
        it->second = soma; 
    }

    for(int i = 0; i < m; i++) {
        long long pos_fisher;
        cin >> pos_fisher;

        auto it = events.upper_bound(pos_fisher);
        if(it == events.begin()) {
            cout << "0\n";
        } else {
            cout << prev(it)->second << "\n";
        }
    }

    return 0;
}