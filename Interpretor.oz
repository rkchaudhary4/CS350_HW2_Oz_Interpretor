\insert 'SingleAssignmentStore.oz'
\insert 'helpers.oz'
\insert 'Unify.oz'
declare SStack Pop Push
SStack = {NewCell nil}

proc {Push SStack  S E}
    case S of 
    nil then 
        skip
    else 
        SStack := semanticStatement(S E) | @SStack 
    end
end

fun {Pop SStack}
    case @SStack of nil then nil
    else
        local H = @SStack.1 in
            SStack := @SStack.2
            H
        end
    end
end

proc {Interpret SStack}
    case @SStack of nil then {Browse 'Program finished'}
    else
        case {Pop SStack} of
            semanticStatement([match ident(X) P S1 S2] E) then
                local ValOfX Match Enew in
                    ValOfX = {RetrieveFromSAS E.X}
                    if ValOfX.1 \= record then raise 'Variable not a record' end
                    elseif P.1 \= record then {Push SStack S2 E}
                    else 
                        case ValOfX of equivalence(_) then
                            raise 'Variable not bound' end
                        else
                            {MatchBind ValOfX P E Match Enew}
                            if Match == true then {Push SStack S1 Enew} else {Push SStack S2 E} end
                        end
                    end
                end
            [] semanticStatement([nop] E) then
                skip
            [] semanticStatement([var ident(X) S] E) then
                {Push SStack S {Adjoin E environment(X:{AddKeyToSAS})}}
            [] semanticStatement([bind ident(X) ident(Y)] E) then
                {Unify ident(X) ident(Y) E}
            [] semanticStatement(S1|S2 E) then
                {Push SStack S2 E}
                {Push SStack S1 E}
            [] semanticStatement([bind X1 Y1] E) then
                local X V in
                    case X1 of ident(X2) then
                        X = X2
                        V = Y1
                    else 
                        case Y1 of ident(X2) then
                            X = X2
                            V = X1
                        else raise 'Unknown Statement' end
                        end
                    end
                    case V of [po Args Stmt]
                    then local Closure in
                        Closure = {CalcClosure Stmt {AdjoinList E {Map Args fun {$ A} case A of ident(X) then X#0 else raise 'Wrong Argument' end end end}}}
                        {Unify ident(X) procedure(Args Stmt Closure) E}
                    end
                    else {Unify ident(X) V E}
                    end
                end
            [] semanticStatement(apply|ident(F)|Xs E) then
            local ValOfX in
                ValOfX = {RetrieveFromSAS E.F}
                case ValOfX
                of procedure(ArgList S Closure) then
                    if {Length ArgList} \= {Length Xs} then raise 'wrong arguments to proc' end
                    else
                        local NC in
                            NC = {ArgsInClosure ArgList Xs Closure E}
                            {Push SStack S NC}
                        end
                    end
                [] equivalence(_) then
                raise 'unbound proc' end
                else raise 'variable is not a procedure' end
                end
            end
            else skip end
            {Interpret SStack}
    end
end

% Add a variable Program for the program you want to run, you may uncomment the given program for testing
% Use [po [ident(X1) ....] s] for procedures
%declare Program
%Program = [var ident(foo)
% 			 [var ident(bar)
% 			  [var ident(quux)
% 			   [[bind ident(bar) [po [ident(baz)]
% 					      [bind [record literal(person)
% 						     [literal(age) ident(foo)]] ident(baz)]]]
% 			    [apply ident(bar) ident(quux)]
% 			    [bind [record literal(person) [literal(age) literal(40)]] ident(quux)]
%			    [bind literal(40) ident(foo)]]]]]

{Push SStack Program environment()}
{Interpret SStack}
{Browse 'Thank you for using our interpreter' }