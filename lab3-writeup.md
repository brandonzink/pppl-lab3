Brandon Zink
Cameron Connor

2a. 

var x = 5;

function func_1(){
    var x = 7;
    func_2;
}

func_2(){
    return x;
}

print func_1();

In a static scoped enviroment, the print would output "5" since x was bound to 5 in the scope and not rebound
within the same scope as the print statement. In a dynamically scoped enviroment, the print would output "7"
since x was more recently bound in func_1().

Static scoping works in the way that most languages currently work (C++, Java, Python) where the varaible is bound
inside of a function call or within brackets or what not. Dynamic scoping bind the variable to the most recent call.


3d. 

Yes, the evaluation order is deterministic as specified by the judgement form e -> e'. Some uch binary operation
between e1 and e2 (e -> e') would show it as being left associative.


4. 

All of the figures below are left associative, where the left side of the expression with evaluate before the
right side in the inner most area. In order to change it to being right side associative, you would need to search
to instead step e2 instead of e1, as well as the do rules to instead check for values that are on the right side
of the expression.


5. 


These questions can be answered at the same time. Short circuting is useful because it can end code early if some
condition applies, such as in the AND function. if(e1) then e2 else false. Once e1 is evaluated, if it is false,
the e2 never runs and thus it is short circuted since the code is left side associative. 



