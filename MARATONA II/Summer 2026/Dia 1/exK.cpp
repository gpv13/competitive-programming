#include<bits/stdc++.h>
using namespace std;

//********************************* */
//A FAZER
/////////////////////////////////////

int main(){

    int t;
    cin >> t;
    while(t--){
        int n;
        cin >> n;
        vector<int> atk(n), def(n);
        list<pair<int,int>> stats;
        for(int i=0;i<n;i++){
            cin >> atk[i];
        }
        for(int i=0;i<n;i++)cin >> def[i];
        for(int i = 0;i<n;i++){
            stats.push_back({atk[i], def[i]});
        }
        bool deuZero = false;
        set<list<pair<int,int>>::iterator> candidatos;
        vector<int> ans;
        for(auto it = stats.begin();it!=stats.end();it++) candidatos;
        while(!stats.empty()){
            int contaMortos = 0;
            
            for(auto it = stats.begin(); it != stats.end(); it++){
                int dano = 0;
                if(it != stats.begin()){
                    dano+= (*prev(it)).first;
                }
                if(next(it) != stats.end()){
                    dano+= (*next(it)).first;
                }
                if(dano>(*it).second){
                    contaMortos++;
                    if(it != stats.begin()){
                        candidatos.insert(prev(it));
                    }
                    if(next(it) != stats.end()){
                        candidatos.insert(next(it));
                    }
                    stats.erase(it);
                }
            }
            
            if(!contaMortos) deuZero = true;
            if(deuZero) break;
            ans.push_back(contaMortos);
        }

        // for(int i=0;i<n;i++){
        //     int contaMortos = 0;
        //     if(!i){
        //         for(auto it = stats.begin(); it != stats.end(); it++){
        //             int dano = 0;
        //             if(it != stats.begin()){
        //                 dano+= (*prev(it)).first;
        //             }
        //             if(next(it) != stats.end()){
        //                 dano+= (*next(it)).first;
        //             }
        //             if(dano>(*it).second){
        //                 contaMortos++;
        //                 if(it != stats.begin()){
        //                     candidatos.insert(prev(it))
        //                 }
        //                 if(next(it) != stats.end()){
        //                     candidatos.insert(next(it));
        //                 }
        //             }
        //         }
        //     }
        //     else if(!deuZero){

        //     }
        //     if(!contaMortos) deuZero = true;

        //     if(!i)cout << contaMortos;
        //     else cout << " " << contaMortos; 
        // }
        // cout << endl;
    }


    return 0;
}