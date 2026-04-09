#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    vector<bool> jaUsados(1000001, false);

    while(t--){

        long long n;
        cin >> n;
        vector<vector<int>> blogs(n);
        long long maior = -1;
        for(int i=0;i<n;i++){

            int l;
            cin >> l; 
            // unordered_set<int>aux;
            int last = -1;
            for(int j=0;j<l;j++){
                long long user;
                cin >> user;
                if(last!=-1){
                    if(last!=user)blogs[i].push_back(user);
                }else{
                    blogs[i].push_back(user);
                }
                last = user;
                // aux.insert(user);
            }
            // for(auto s : aux){
            //     blogs[i].push_back(s);
            // }
            reverse(blogs[i].begin(), blogs[i].end());

        }
        sort(blogs.begin(),blogs.end());
        queue<int> fila;
        // for(int i=0;i<n;i++){
        //     for(auto nu : blogs[i]){
        //         if(!jaUsados[nu]){

        //             fila.push(nu);
        //             jaUsados[nu] = true;
        //         }
        //     }
        // }

        // for(auto v:blogs){
        //     for(auto mk : v) cout << " " << mk;
        //     cout << endl;
        // }
        vector<int> posEmCadaBlog(n, 0);

        for(int i=0;i<n;i++){

            int menor = INT32_MAX, vetormenor = -1;
            for(int j=0;j<n;j++){
                while(posEmCadaBlog[j] < blogs[j].size() && jaUsados[blogs[j][posEmCadaBlog[j]]]){
                    posEmCadaBlog[j]++;
                }
                if(posEmCadaBlog[j] >= blogs[j].size())continue;
                if(blogs[j][posEmCadaBlog[j]] < menor){
                    menor = blogs[j][posEmCadaBlog[j]];
                    vetormenor = j;
                }
            }
            if(vetormenor == -1)continue;

            for(int j=posEmCadaBlog[vetormenor];j<blogs[vetormenor].size();j++){
                if(!jaUsados[blogs[vetormenor][j]]) {fila.push(blogs[vetormenor][j]); jaUsados[blogs[vetormenor][j]] = true;} //aumentar o posemcadablogdesse
                posEmCadaBlog[vetormenor]++;
            }
        }



        bool primeiro = true;
        
        while(!fila.empty()){
            if(primeiro) cout << fila.front();
            else cout << " " << fila.front();
            primeiro = false;
            jaUsados[fila.front()] = false;
            fila.pop();
        }
        cout << endl;
        

    }


    return 0;
}
/*5
5 1 1 1 1 1
5 1 2 3 4 5
1
18
3 2 2 2
3 1 2 3
1 2 3 5 4 18*/