#include <bits/stdc++.h>
using namespace std;

vector<bool> prime(100002, true);

void SieveOfEratosthenes(int n){

    for (int p = 2; p * p <= n; p++) {


        if (prime[p] == true) {
            for (int i = p * p; i <= n; i += p)
                prime[i] = false;
        }
    }
}
int main()
{
    int n;
    vector<int> notas;
    SieveOfEratosthenes(100001);
    cin >> n;
    for(int i=0;i<n;i++){
        int nota;
        cin >> nota;
        notas.push_back(nota);
    }
    int q;
    cin >> q;
    for(int i=0;i<q;i++){
        float taxa;
        cin >> taxa;
        set<int> ord;
        int ant = -1;
        for(int j=n-1;j>=0;j--){
            int result = notas[j] * taxa;
            while(!prime[result] || result == ant){
                result--;
            }
            ant = result;
            ord.insert(result);
        }
        bool first = true;
        for(auto c: ord){
            if(!first) cout << " ";
            cout << c;
            first = false;
        }
        cout << endl;
    }
    

    return 0;
}