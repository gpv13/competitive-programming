#include <bits/stdc++.h>
using namespace std;
#define mod 1000000000
int main() {
    long long int q;
    cin >> q;
    set<long long int> b;
    vector<long long int> a;
    long long int resp = 0;
    for(long long int i=0;i<q;i++){
        long long int y, x;
        cin >> y;
        a.push_back(((y+resp)%mod)+1);
        b.insert(((y+resp)%mod)+1);
        int aux = 1;
        resp = 0;
        for(auto num: b){
            if(aux%2 !=0){
                resp+=num;
            }
            aux++;
        }
        cout << resp << endl;

    }
    return 0;
}
