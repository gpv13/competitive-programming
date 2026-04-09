#include<bits/stdc++.h>
#include<string>
using namespace std;

bool temDuploAst(string rio){
    for(int i = 1; i<rio.size(); i++){
        if(rio[i] == '*' && (rio[i-1] == '*' || rio[i-1] == '>')){
            return true;
        }   
    }
    for(int i = 0; i<rio.size() - 1; i++){
        if(rio[i] == '*' && (rio[i+1] == '<')){
            return true;
        }    
    }
    return false;
}

bool temLoop(string rio){

    bool achouDir = false;
    for(int i = 0; i<rio.size(); i++){
        if(rio[i] == '>'){
            achouDir = true;
        }
        if(achouDir && rio[i] == '<'){
            return true;
        }
    }
    return false;
}

int main(){

    int t;
    cin >> t;
    while(t--){

        string rio;
        cin >> rio;
        int countUm = 0, countDois = 0;
        if(temDuploAst(rio) || temLoop(rio)) cout << "-1" << endl;
        else if(rio.size() == 1) cout << "1" << endl;
        else{
        for(int i = 0; i<rio.size(); i++){
            if(rio[i] == '>'){
                countUm = i;
                break;
            }    
        }
        for(int i = rio.size()-1; i>=0 ;i--){
            
            if(rio[i] == '<'){
                break;
            }
            countDois++;
        }
            cout << max(countDois, countUm) << endl;
        }


    }



    return 0;
}
