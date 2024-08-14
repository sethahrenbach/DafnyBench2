predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
requires 0<=start<=end<=a.Length       
reads a       
{           
  forall j,k:: start<=j<k<end ==> a[j]<=a[k]
}

method InsertionSort (a:array<int>)
requires a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{  
    var up := 1;   
    
    while (up < a.Length)   // outer loop
    invariant 1 <= up <= a.Length
    invariant sorted(a, 0, up)   
    {  
        var down := up-1;
        var temp := a[up];
        
        while down >= 0 && temp < a[down]    // inner loop
        invariant -1 <= down < up
        invariant forall i :: down+1 <= i <= up ==> a[i] >= temp
        invariant forall i :: 0 <= i <= down ==> a[i] <= old(a[down+1])
        invariant forall i :: up+1 <= i < a.Length ==> a[i] == old(a[i])
        invariant temp == old(a[up])
        {
            a[down+1] := a[down];           
            down := down-1;       
        }
        a[down+1] := temp;
        assert sorted(a, 0, up+1);            
        up := up+1;
           
    }
}      

method Main(){
  var a := new int[5];
  a[0],a[1],a[2],a[3],a[4] := 3,2,5,1,8;
  InsertionSort(a);
  print a[..];
}