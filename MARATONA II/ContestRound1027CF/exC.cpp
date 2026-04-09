#include<bits/stdc++.h>
using namespace std;

int main(){

    int t;
    cin >> t;
    for(int k = 0;k<t;k++){

        int n;
        cin >> n;
        int quantArrays = 1 , num, ant;
        for(int i=0;i<n;i++){
            cin >> num;
        
            if(i!=0){

                if(num > ant + 1){
                    quantArrays++;
                    ant = num;
                }

            }else{
                ant = num;
            }
        }


        cout << quantArrays << endl;

    }



    return 0;
}