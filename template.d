// dfmt off
T lread(T=long)(){return readln.chomp.to!T;}T[] lreads(T=long)(long n){return iota(n).map!((_)=>lread!T).array;}
T[] aryread(T=long)(){return readln.split.to!(T[]);}void arywrite(T)(T a){a.map!text.join(' ').writeln;}
void scan(L...)(ref L A){auto l=readln.split;foreach(i,T;L){A[i]=l[i].to!T;}}alias sread=()=>readln.chomp();
void dprint(L...)(lazy L A){debug{auto l=new string[](L.length);static foreach(i,a;A)l[i]=a.text;arywrite(l);}}
alias PQueue(T,alias l="b<a")=BinaryHeap!(Array!T,l);import std, core.bitop;
// dfmt on
{% if mod %}immutable long MOD = {{ mod }};{% endif %}
{% if yes_str %}immutable string YES = "{{ yes_str }}";{% endif %}
{% if no_str %}immutable string NO = "{{ no_str }}";{% endif %}
void main()
{
    {% if prediction_success %}
    {{ input_part }}
    solve({{ actual_arguments }});
    {% else %}
    // Failed to predict input format
    {% endif %}
}

{% if prediction_success %}
void solve({{ formal_arguments }}){

}
{% endif %}