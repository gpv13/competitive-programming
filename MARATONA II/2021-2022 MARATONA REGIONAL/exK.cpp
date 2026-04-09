#include<bits/stdc++.h>
using namespace std;

int main(){

    int t, d, m;
    vector<int> meals;
    bool sleep = false;
    cin >> t >> d >> m;
    for(int i=0;i<m;i++){
        int aux;
        cin >> aux;
        meals.push_back(aux);
    }
    if(t > d){
        sleep = false;
    }else if(m == 0){
        if(t<=d){
            sleep = true;
        }
    
    }
    else{
        if(meals[0] >= t){
            sleep = true;
        }
        for(int i=1;i<m;i++){
            if(meals[i] - meals[i-1] >= t){
                sleep = true;
            }
        }
        if(d - meals[m-1] >= t){
            sleep = true;
        }
    }
    if(sleep){
        cout << "Y" << endl;
    }else{
        cout << "N" << endl;
    }


    return 0;
}