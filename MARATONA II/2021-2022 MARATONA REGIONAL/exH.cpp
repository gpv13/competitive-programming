#include<bits/stdc++.h>
using namespace std;

int main(){
    bool check = true;
    vector<pair<int, int>> list;
    int n, k;
    cin >> n >> k;
    for(int i =0; i<n;i++){
        pair<int,int> aux;
        cin >> aux.first >> aux.second;
        list.push_back(aux);
    }
    for(int i =0; i<n;i++){
        if(list[list[i].first - 1].second != list[i].second){
            check = false;
            break;
        }
    }
    if(check){
        cout << "Y" << endl;
    }else{
        cout << "N" << endl;
    }

    return 0;
}