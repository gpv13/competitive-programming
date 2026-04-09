#include<bits/stdc++.h>
using namespace std;
set<string> y;
set<string> x;
bool comp(string n){
    if(y.compare(0, n.end(), n) == 0){
        return true;
    }else{
        return false;
    }
}
void esta(){
    for(auto nm : x){
        if(comp(*lower_bound(y.begin(), y.end(), nm, comp(nm)))){
            y.erase(*lower_bound(y.begin(), y.end(), nm, comp(nm)));
        }
    }
}
int main(){
    int q;
    cin >> q;
    for(int i =0; i<q;i++){
        int tipo;
        string nm;
        cin >> tipo >> nm;
        if(tipo == 1){
            x.insert(nm);
        }else{
            y.insert(nm);
        }
        esta();
        cout << y.size() << endl;
    }

    return 0;
}