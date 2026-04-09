#include<bits/stdc++.h>
using namespace std;

vector<int> z_function(string s) {
    int n = s.size();
    vector<int> z(n);
    int l = 0, r = 0;
    for(int i = 1; i < n; i++) {
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

    int t;
    cin >> t;
    while(t--){
        string s;
        cin >> s;
        string palPre;
        int posComeco = 0;
        int tamaux= s.size();
        if(tamaux%2) tamaux-=2;
        for(int i = 0; i <((tamaux/2.0));i++){
            if(s[i] == s[s.size()-1-i]){
                posComeco++;
                palPre+=s[i];
            }else{
                break;
            }
        }
        string reconst1, reconst2;
        for(int i=posComeco;i<s.size()-posComeco;i++) reconst1+=s[i];
        string aux = reconst1;
        int tam = aux.size();
        reverse(aux.begin(),aux.end());
        reconst2 = aux + '*' + reconst1;
        reconst1 += '*';
        reconst1 += aux;
        // cout << reconst1 << endl;
        vector<int> z = z_function(reconst1), z2 = z_function(reconst2);

        // for(auto n : z){
        //     cout << n << " ";
        // } cout << endl;

        int ind1 = -1, ind2 = -1;
        for(int i=tam+1;i<reconst1.size();i++){
            
            if(ind1 == -1 && z[i] != 0 && z[i] == reconst1.size()-i) ind1 = i;
            else if(z[i] != 0 && z[ind1] < z[i] && z[i] == reconst1.size()-i) ind1 = i;
        
            if(ind2 == -1 && z2[i] != 0 && z2[i] == reconst2.size()-i) ind2 = i;
            else if(z2[i] != 0 && z2[ind2] < z2[i] && z2[i] == reconst2.size()-i) ind2 = i;
        }
        string meio;
        if(ind1 != -1 || ind2 != -1){
            if(z[ind1]>z2[ind2]){
                for(int i=ind1;i<reconst1.size();i++) meio+=reconst1[i];
            }
            else for(int i=ind2;i<reconst2.size();i++) meio+=reconst2[i];
        }
        string cont = palPre;
        reverse(cont.begin(), cont.end());
        if(s.size() == 1) cont = "";
        // cout << palPre << " " << meio << " " << cont << endl;
        string resp = palPre + meio + cont;
        cout << resp << endl;       
    }
     


    return 0;
}