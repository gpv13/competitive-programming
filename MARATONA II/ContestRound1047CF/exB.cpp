#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    while(n--){

        int t;
        cin >> t;
        vector<int> lista;
        vector<bool> teste(t+1, false);
        vector<int> res;
        for(int i=0; i<t;i++){

            int aux;
            cin >> aux;

            int mod = 3 - (aux%3);
            int mod2 = 0;
            while(aux % 3 != 0){
                aux--;
                mod2++;
            }
            int auxiliar = t - mod2++
            while(teste[mod2 - aux]){
                mod2 -= 3;
                cout << mod2 << " ";
            }
            teste[mod2 - aux] = true;

            cout << aux << " ";
            res.push_back(mod2 - aux);


        }
        bool primeiro = true;
        for(int num : res){
            if(primeiro) cout << num;
            else cout << " " << num;

            primeiro = false;
        }
        cout << endl;
    }



    return 0;
}