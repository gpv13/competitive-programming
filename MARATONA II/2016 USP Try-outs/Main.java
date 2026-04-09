import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        int n, m;
        Scanner s = new Scanner(System.in);
 
        n = s.nextInt();
        m = s.nextInt();
        long listaTaylor[] = new long[n];
        for(int i=0;i<n;i++){
            listaTaylor[i] = s.nextLong();;
        }
        long listaKaty[] = new long[m]; 

        for(int i=0;i<m;i++){
            listaKaty[i] = s.nextLong();;
        }


        HashMap<BigInteger, Integer> mapTaylor = new HashMap<>(); 
        int limitTaylor = 1 << n;
        for(int mask=1;mask<limitTaylor;mask++){

            BigInteger product = BigInteger.ONE;
            for(int bit = 0;bit<n;bit++){
                if((mask & (1 << bit)) != 0)product = product.multiply(BigInteger.valueOf(listaTaylor[bit]));
            }

            mapTaylor.put(product, mask);
        }
        int limitKaty = 1 << m;
        for(int mask=1;mask<limitKaty;mask++){

            BigInteger product = BigInteger.ONE;
            for(int bit = 0;bit<m;bit++){
                if((mask & (1 << bit)) != 0)product = product.multiply(BigInteger.valueOf(listaKaty[bit]));
            }

            if(mapTaylor.containsKey(product)){
                int maskTaylor = mapTaylor.get(product);

                System.out.println("Y");
                printSolution(listaTaylor, maskTaylor, listaKaty, mask);
                return;
            }
        }
        System.out.println("N");
    }
    private static void printSolution(long[] listaTaylor, int maskTaylor, long[] listaKaty, int mask){
        ArrayList<Long> listT = new ArrayList<>();
        ArrayList<Long> listK = new ArrayList<>();
        for(int i=0;i<listaTaylor.length;i++){
            if((maskTaylor & (1 << i)) != 0) listT.add(listaTaylor[i]);
        }
        for(int i=0;i<listaKaty.length;i++){
            if((mask & (1 << i)) != 0) listK.add(listaKaty[i]);
        }
        boolean primeiro = true, segundo = true;

        System.out.println(listT.size() + " " + listK.size());

        for(int i=0;i<listT.size();i++){
            if(primeiro)System.out.print(listT.get(i));
            else System.out.print(" " + listT.get(i));
            primeiro = false;
        } 
        System.out.println();
        for(int i=0;i<listK.size();i++){
            if(segundo)System.out.print(listK.get(i));
            else System.out.print(" " + listK.get(i));
            segundo = false;
        } 
        System.out.println();
    }
}
