#include<bits/stdc++.h>
using namespace std;


int main(){

    int n, k;
    cin >> n >> k;
    vector<int> todos(n), combs;
    for(int i=0;i<n;i++){

        int aux;
        cin >> aux;
        todos[i] = aux;
    }
    for(int i=0;i<n;i++){
        for(int j=i + 1;j<n;j++){
            combs.push_back(todos[i] + todos[j]);
        }
    }
    sort(combs.begin(), combs.end());
    cout << combs[k-1] << endl;

    return 0;
}