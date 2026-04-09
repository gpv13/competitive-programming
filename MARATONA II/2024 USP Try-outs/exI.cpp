#include<bits/stdc++.h>
using namespace std;

int main(){

    int n;
    cin >> n;
    bool todosUm = true, todosPares = true;

    while(n--){
        int num;
        cin >> num;
        if(num == 0) continue;
        if(num!=1) todosUm = false;
        if(num%2 != 0) todosPares = false;
    }
    if(todosPares || todosUm) cout << "1" << endl;
    else cout << "2" << endl;

    return 0;
}