#include <bits/stdc++.h>

using namespace std;


struct Ponto{
    long long x, y;
};

Ponto p0;

double distSq(Ponto p1, Ponto p2){
    return (double)((double)(p1.x - p2.x)*(p1.x - p2.x) + (double)(p1.y - p2.y)*(p1.y - p2.y)); 
}

int orientacao(Ponto p, Ponto q, Ponto r){
    long long val = (long long)(q.y - p.y)*(r.x - q.x) - (long long)(q.x - p.x)*(r.y - q.y);

    if(val == 0) return 0;
    return (val > 0) ? 2 : 1;
}

bool compararPontos(Ponto p1, Ponto p2){
    int o = orientacao(p0, p1, p2);

    if( o == 0){
        return distSq(p0, p1) < distSq(p0, p2);
    }
    return (o == 2);
}

vector<Ponto> grahamScan(vector<Ponto>& pontos){
    int n = pontos.size();
    if(n<3) return pontos;

    int min_y = pontos[0].y, min_idx = 0;
    for(int i=1; i<n;i++){
        int y = pontos[i].y;
        if((y<min_y) || (y == min_y && pontos[i].x < pontos[min_idx].x)){
            min_y = pontos[i].y;
            min_idx = i;
        }
    }

    swap(pontos[0], pontos[min_idx]);

    p0 = pontos[0];

    sort(pontos.begin() + 1, pontos.end(), compararPontos);

    int m =1;

    for(int i = 1; i<n; i++){
        while(i < n-1 && orientacao(p0, pontos[i], pontos[i+1]) == 0){
            i++;
        }
        pontos[m] = pontos[i];
        m++;
    }

    if(m<3) return {pontos[0], pontos[m-1]};

    stack<Ponto> fecho_stack;
    fecho_stack.push(pontos[0]);
    fecho_stack.push(pontos[1]);
    fecho_stack.push(pontos[2]);

    for(int i = 3; i< m; i++){
        while(fecho_stack.size() > 1){
            Ponto top = fecho_stack.top();
            fecho_stack.pop();
            Ponto next_to_top = fecho_stack.top();
            fecho_stack.push(top);

            if(orientacao(next_to_top, top, pontos[i]) == 1){
                fecho_stack.pop();
            } else {
                break;
            }
        }
        fecho_stack.push(pontos[i]);
    }

    vector<Ponto> resultado;

    while(!fecho_stack.empty()){
        resultado.push_back(fecho_stack.top());
        fecho_stack.pop();
    }

    reverse(resultado.begin(), resultado.end());
    
    return resultado;
}

bool estaForaFunc(vector<Ponto>pontos, Ponto fugitivo){

    bool fora = false;

    for(int i=0;i<pontos.size() - 1; i++){
        if(orientacao(pontos[i], pontos[i+1], fugitivo) == 1){

            fora = true;
            break;

        }
    }
    if(orientacao(pontos[pontos.size() - 1], pontos[0], fugitivo) == 1){
        fora = true;
    }

    return fora;
}



int main(){

    int x, y;
    Ponto P, fugitivo;
    vector<Ponto> pontos;
    for(int i =0; i<5; i++){
        cin >> x >> y;
        P.x = x; P.y = y;
        if(i == 4){
            fugitivo.x = x;
            fugitivo.y = y;
        }else{
            pontos.push_back(P);
        }
    }
    int min_y = pontos[0].y, min_idx = 0;
    for(int i=1; i<pontos.size();i++){
        int y = pontos[i].y;
        if((y<min_y) || (y == min_y && pontos[i].x < pontos[min_idx].x)){
            min_y = pontos[i].y;
            min_idx = i;
        }
    }

    swap(pontos[0], pontos[min_idx]);

    p0 = pontos[0];

    sort(pontos.begin() + 1, pontos.end(), compararPontos);
    //vector<Ponto> fecho = grahamScan(pontos);
    bool EstaFora = estaForaFunc(pontos, fugitivo);
    
    

    bool saoColineares = true;
    if(orientacao(pontos[0], pontos[1], pontos[2]) != 0) saoColineares = false;
    if(orientacao(pontos[0], pontos[1], pontos[3]) != 0) saoColineares = false;
    if(orientacao(pontos[1], pontos[2], pontos[3]) != 0) saoColineares = false;

    if(saoColineares) EstaFora = true;

    if(EstaFora){

        cout << " O>" << endl;
        cout << "<| " << endl;
        cout << "/ >" << endl;
    }else{
        cout << "\\O/" << endl;
        cout << " | " << endl;
        cout << "/ \\" << endl;
    }


return 0;
}