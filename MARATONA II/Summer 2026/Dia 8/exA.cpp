#include<bits/stdc++.h>
using namespace std;

#define INF 1e13


vector<long long int> z_function(vector<long long int> s) {
    long long int n = s.size();
    vector<long long int> z(n);
    long long int l = 0, r = 0;
    for(long long int i = 1; i < n; i++) {
        if(i < r) {
            z[i] = min(r - i, z[i - l]);
        }
        while(i + z[i] < n && s[z[i]] == s[i + z[i]]) {
            z[i]++;
        }
        if(i + z[i] > r) {
            l = i;
            r = i + z[i];
        }
    }
    return z;
}

int main(){

    long long int u, e;
    cin >> u >> e;
    vector<long long int> torresUrso(u), torresEle(e);
    vector<long long int> difU, difE;
    // string torresU, torresE;
    for(long long int i=0;i<u;i++){
        cin >> torresUrso[i];
        if(i){
            // if(torresUrso[i] - torresUrso[i-1] >= 0) {torresU += ((torresUrso[i] - torresUrso[i-1])+'0'); torresU += " ";}
            // else {
            //     torresU += '-'; 
            //     torresU += (abs(torresUrso[i] - torresUrso[i-1]) + '0');
            //     torresU += " ";
            // }
            difU.push_back(torresUrso[i] - torresUrso[i-1]);
        }
    }
    for(long long int i=0;i<e;i++){
        cin >> torresEle[i];
        if(i){
            // if(torresEle[i] - torresEle[i-1] >= 0) {torresE += ((torresEle[i] - torresEle[i-1])+'0'); torresE += " ";}
            // else{
            //     torresE += '-';
            //     torresE += (abs(torresEle[i] - torresEle[i-1]) + '0');
            //     torresE += " ";
            // }
            difE.push_back(torresEle[i] - torresEle[i-1]);
        }
    }
    
    vector<long long int> aux = difE;
    aux.push_back(INF);
    for(int i=0;i<difU.size();i++){
        aux.push_back(difU[i]);
    }
    // string aux = torresE + '*' + torresU;
    // for(auto c : aux) cout << c << " ";
    // cout << endl;
    long long int conta = 0;
    // long long int ini = ceil((double)aux.size()/2.0);
    vector<long long int> z = z_function(aux);
    // for(auto c : z) cout << c << " ";
    // cout << endl;


    for(long long int i=difE.size()+1;i<aux.size();i++){
        if(z[i] == difE.size()) conta++;
    }
    if(e == 1) cout << u << endl;
    else cout << conta << endl;


    return 0;
}