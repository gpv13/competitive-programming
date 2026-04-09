#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    for(int i=0;i<n;i++){

        bool iguais = false, segundoigual1 = false;
        int num1, num2;
        cin >> num1 >> num2;
        if(num1 == num2){
            iguais = true;
        }
        if(num2 == 1){
            segundoigual1 = true;
        }

        if(iguais || segundoigual1 || num1 - num2 == 1){
            cout << "-1" << endl;
        }else{
            if(num1 < num2){
                cout << "2" << endl;
            }else{
                cout << "3" << endl;
            }
        }

    }

    return 0;
}