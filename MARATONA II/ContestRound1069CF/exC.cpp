#include<bits/stdc++.h>
using namespace std;



int main(){

    int n;
    cin >> n;
    while(n--){

        string s, t;
        
        cin >> s;
        cin >> t;
        vector<int> ans(27, 0), phrase(27, 0);
        for(auto c : s) ans[c-'a' + 1]++;
        for(auto c : t) phrase[c-'a' + 1]++;

        bool possible = true;

        for(int i=1;i<=26;i++){
            if(ans[i] > phrase[i]) possible = false;
        }

        if(!possible) cout << "Impossible" << endl;
        else{

            int pointerAns = 0, pointerPhrase = 0;
            while(pointerAns < s.length() || pointerPhrase < 27){

                // while(ans[pointerAns] == 0){
                //     pointerAns++;
                // }
                while(phrase[pointerPhrase] ==  ans[pointerPhrase]) pointerPhrase++;
                while(phrase[pointerPhrase] == 0 && pointerPhrase < 27){
                    pointerPhrase++;
                }
                if(pointerPhrase >= s[pointerAns]-'a'+1 && pointerAns < s.length()){
                    cout << s[pointerAns];
                    pointerAns++;
                }else if(pointerPhrase < 27){
                    char aux = pointerPhrase + 'a' - 1;
                    cout << aux;
                    phrase[pointerPhrase]--;
                }


            }
            cout << endl;
        }

    }


    return 0;
}