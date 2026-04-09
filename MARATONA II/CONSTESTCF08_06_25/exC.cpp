#include<bits/stdc++.h>
using namespace std;

#define NMAX 200001

int main(){

    int q;
    cin >> q;
    
    for(int i=0;i<q;i++){
        vector<int> nums(NMAX);
        int l;
        cin >> l;
        for(int j=0;j<l;j++){
            int n;
            cin >> nums[j];
        }
        set<int> verific;
        set<int> aux;
        int divisoes = 0;
        aux.insert(nums[0]);
        //aux = verific;
    
        divisoes++;
        for(int j=1;j<l;j++){

            set<int> difference;
    

            verific.insert(nums[j]);

            // if(verific.count(nums[j])){
            //     aux.insert(nums[j]);
            // }
            
            set_difference(aux.begin(), aux.end(), verific.begin(), verific.end(), inserter(difference, difference.begin()));

            if(difference.empty()){
                //cout << "vazio : " << endl;
                //for(auto c: aux) cout << c << " ";
                //cout << endl;
                //for(auto c: verific) cout << c << " ";
                //cout << endl;
                divisoes++;
                aux = verific;
                verific.clear();
            }
        }

        //fiz esses fors so pra verificar oq estava entrando no aux e no verific
        // for(auto c: aux) cout << c << " ";
        // cout << endl;
        // for(auto c: verific) cout << c << " ";
        // cout << endl;

        
        cout << divisoes << endl;
    }

    
    return 0;
}