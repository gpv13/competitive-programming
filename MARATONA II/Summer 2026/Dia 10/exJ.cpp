#include<bits/stdc++.h>
using namespace std;
int main(){


    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    
    long long int n,m,l;
    cin >> n >> m >> l;
    map<long long int,long long int> fish; //pos, +/-
    for(long long int i = 0;i<n;i++){
        long long int x, y;
        cin >> x >> y;
        if(y-l<=0){
            long long int dist = abs(y-l);
            fish[x-dist]++;
            fish[x+dist+1]--;
        }
    }
    map<long long int,long long int> prefix;
    long long int soma = 0;
    for(auto &[i, x] : fish){
        soma+=x;
        prefix[i] = soma; 
    }
    vector<long long int>fisher(m);
    for(long long int i=0;i<m;i++) cin >> fisher[i];
    for(long long int i=0;i<m;i++){
        auto it = prefix.upper_bound(fisher[i]);
        if(it == prefix.begin()){
            cout << "0" << endl;
        }else{
            cout << prev(it)->second << endl;
        }
    }

    return 0;
}