#include<bits/stdc++.h>
using namespace std;
int main(){


    vector<int> countm(501, 0), countastm(501, 0);
    vector<int> countn(17, 0), countastn(17,0);
    string n, m;
    cin >> m;
    cin >> n;

    int import = m.size() - 1;
    for(int i=0;i<m.size();i++){
       
        
            
            if(m[i] == '1'){
                countm[import]++;
            }
            if(m[i] == '*') countastm[import]++;
            import--;
        
    }
    import = n.size() - 1;
    for(int i=0;i<n.size();i++){
       
        
            
            if(n[i] == '1'){
                countn[import]++;
            }
            if(n[i] == '*') countastn[import]++;
            import--;
        
    }
    for(int j=0;j<40;j++){
            if(bits[j]){

                num += pow(2, j);
                bits[j]--;
            }
    }
    

    return 0;
}
