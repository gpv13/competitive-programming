#include <bits/stdc++.h>
using namespace std;
 
struct Edge{
    int to;
    long long int cap;
};
 
const int N=5123,INF=0x3f3f3f3f;
 
int vis[N],anterior[N],aresta[N];
char mat[52][52];
vector<int> g[N];
vector<Edge> edges;
 
void addEdge(int a,int b,int c){
    g[a].push_back(edges.size());
    edges.push_back(Edge{b,c});
    g[b].push_back(edges.size());
    edges.push_back(Edge{a,c});
}
 
int BFS(int ini, int fim){ // 1 se tiver caminho, 0 caso nao
    int i;
    queue<int> fila;
    memset(vis,0,sizeof(vis));
    fila.push(ini); vis[ini] = 1; anterior[ini] = -1;
    while (!fila.empty()){
        int a=fila.front();fila.pop();
        for(auto i:g[a]){
            int b=edges[i].to,c=edges[i].cap;
            if(!vis[b]&&c){
                anterior[b]=a;
                aresta[b]=i;
                if(b==fim) return 1;
                fila.push(b);
                vis[b]=1;
            }
        }
    }
    return 0;
}
 
long long fluxoMaximo(int ini, int fim){
    int u, v;
    long long int fluxo = 0;
    long long int bot;
    while (BFS(ini, fim)){
        bot = INF;
        for (v = fim; v != ini; v = anterior[v]){
            u = aresta[v];
            bot = min(bot, edges[u].cap);
        }
        for (v = fim; v != ini; v = anterior[v]){
            u = aresta[v];
            edges[u].cap -= bot; edges[u^1].cap += bot; 
        }
        fluxo += bot;
    }
    return fluxo;
}
 
int minCut(int s,int m){
    int avis[N];
    set<int> res;
    memset(avis,0,sizeof(avis));
    queue<int> fila;
    fila.push(s); avis[s] = 1;
    while (!fila.empty()){
        int a=fila.front();fila.pop();
        for(auto i:g[a]){
            int b=edges[i].to,c=edges[i].cap;
            if(!vis[b]){
                if(mat[a/m][a%m]=='.') mat[a/m][a%m]='+';
                else mat[b/m][b%m]='+';
                res.insert(b);
            }
            if(!avis[b]&&c){
                fila.push(b);
                avis[b]=1;
            }
        }
    }
    return res.size();
}
 
int main(){
    int n,m,source,sink;
    cin>>n>>m;
    for(int i=0;i<n;i++){
        cin>>mat[i];
    }
    for(int i=0;i<n;i++){
        for(int j=0;j<m;j++){
           if(mat[i][j]=='A') source=i*m+j;
           if(mat[i][j]=='B') sink=i*m+j;
           if(mat[i][j]!='#'){
                if(mat[i][j]=='.'){
                    if(i<n-1){
                        if(mat[i+1][j]!='#') addEdge(i*m+j,(i+1)*m+j,1);
                    }
                    if(j<m-1){
                        if(mat[i][j+1]!='#') addEdge(i*m+j,i*m+j+1,1);
                    }
                }else{
                    if(i<n-1){
                        if(mat[i+1][j]=='.') addEdge(i*m+j,(i+1)*m+j,1);
                        else if(mat[i+1][j]!='#') addEdge(i*m+j,(i+1)*m+j,INF);
                    }
                    if(j<m-1){
                        if(mat[i][j+1]=='.') addEdge(i*m+j,i*m+j+1,1);
                        else if(mat[i][j+1]!='#') addEdge(i*m+j,i*m+j+1,INF);
                    }
                }
           }
        }
    }
    long long int flow=fluxoMaximo(source,sink);
    if(flow>=INF) cout<<"-1\n";
    else{
        minCut(source,m);
        int mais = 0;
        // cout<<flow<<endl;
        for(int i=0;i<n;i++){
            for(int j=0;j<m;j++) if(mat[i][j] == '+') mais++;
        }
        cout << mais << endl;
        for(int i=0;i<n;i++){
            for(int j=0;j<m;j++) cout<<mat[i][j];
            cout<<endl;
        }
    }
    return 0;
}