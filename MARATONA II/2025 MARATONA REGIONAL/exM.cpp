#include<bits/stdc++.h>
using namespace std;

int main(){

    long long int n, k;
    cin >> n >> k;
    vector<long long int> lista(n);
    for(long long int i=0;i<n;i++){
        cin >> lista[i];
    }

    long long int posmenor = 0, posicaomuro = 0, menor = lista[0] + k, murosAfetandoOMenor = k, distAtualParaMenor = 0, distMuroParaMenor = 0;  
    for(int i=1;i<n;i++){
        distAtualParaMenor = i - posmenor;
        distMuroParaMenor = posicaomuro - posmenor;
        long long int murosQueVaoAfetarOMenorSeMudar = max(0LL, k - distAtualParaMenor);
        if(lista[i] < menor - (murosAfetandoOMenor) + murosQueVaoAfetarOMenorSeMudar){ //ou seja vale a pena mudar o local do muro
            posicaomuro = i;
            if(lista[i] + k < menor - (murosAfetandoOMenor) + murosQueVaoAfetarOMenorSeMudar){ //pra atualizar o menor e posicao do menor, ve qual o novo menor dps da mudança do muro
                menor = lista[i] + k;
                posmenor = i;
                murosAfetandoOMenor = k;
            }
            else{ //mantem o mesmo menor
                menor = menor - (murosAfetandoOMenor) + murosQueVaoAfetarOMenorSeMudar; //mudando so quantos muros afetam ele
                murosAfetandoOMenor = murosQueVaoAfetarOMenorSeMudar;  
            }
        }
    }


    //essa ultima parte nao sei se é realmente necssaria, pois o unico erro que estava ocorrendo sem ela era quando o menor estava no fim e o codigo nao passava nele.
    //entao talvez seria so comparar o menor achado acima com o ultimo, mas nao testei isso, pois ia gastar tempo pensando em como o muro agiria nisso e preferi resolver assim, e como o limite nao é grande, mais duas passadas por ele nao tem problema.
    long long int conta = k; 
    for(int i=posicaomuro; i>max(-1LL, posicaomuro - k); i--){ //usa esse for pra somar os muros nas posicoes que eles devem estar, que foi encontrado acima
        lista[i]+=conta;
        conta--;
    }
    long long int result = LLONG_MAX; 
    for(int i=0;i<n;i++){ //aqui faz uma passada pela lista pra ver dps da adicao do muro qual é o menor real;
        result = min(result, lista[i]);
    }
    cout << result << endl;


    return 0;
}