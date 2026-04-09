#include <bits/stdc++.h>
using namespace std;

void simplifica(long long& x, long long& y){
    long long g = __gcd(x,y);
    x/=g; y/=g;
}
//3.500.000.000.000.000 5.243.637.857.891.291
void solve() {
    long long x, y;
    cin >> x >> y;
    // simplifica(x,y);
    // double div = (double)x/(double)y;
    bool bob = true;
    if(3*x >= 2*y && x<y){
        bob=true;
    }else{
        bob=false;
    }
    cout << (bob ? "Bob" : "Alice") << endl;
}

int main() {
    int t;
    cin >> t;
    while (t--) {
        solve();
    }
    return 0;
}