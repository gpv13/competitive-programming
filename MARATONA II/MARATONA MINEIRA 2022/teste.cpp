#include<bits/stdc++.h>
using namespace std;

// MDC - Algoritmo de Euclides - O(log(min(a, b)))
int gcd(int a, int b) {
    while (b) {
        a %= b;
        // Troca os valores de a e b
        int temp = a;
        a = b;
        b = temp;
    }
    return a;
}

int main(){

    cout << gcd(2, 5);


    return 0;
}