\insert 'SingleAssignmentStore.oz'
\insert 'helpers.oz'
declare SStack Pop Push
SStack = {NewCell nil}

proc {Push SStack  S E}
    case S of 
    nil then 
        skip
    else 
        SStack := sematicStatement(S E) | @SStack 
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
            sematicStatement([match ident(x) p s1 s2] E) then
                local ValOfX Match Enew in
                    ValOfX = {RetrieveFromSAS E.x}
                    if ValOfX.1 \= record then raise notRecord(x) end
                    elseif p.1 \= record then {Push SStack s2 E}
                    else 
                        case ValOfX of equivalence(_) then
                            raise unbound(x) end
                        else
                            {MatchBind ValOfX p E Match Enew}
                            if Match == true then {Push SStack s1 Enew} else {Push SStack s2 E} end
                        end
                    end
                end
            [] semanticStatement([nop] E) then 
                skip
            [] semanticStatement([var ident(X) s] E) then
			    {Push SemanticStack s {Adjoin E environment(X:{AddKeyToSAS})}}
            [] semanticStatement([bind ident(X) ident(Y)] E) then
			    {Unify ident(X) ident(Y) E}
            [] semanticStatement(apply|ident(f)|xs E) then
            local ValOfX in
                ValOfX = {RetrieveFromSAS E.f}
                case ValOfX
                of procedure(ArgList S closure) then
                    if {Length ArgList} \= {Length xs} then raise 'wrong arguments to proc' end
                    else
                        local NC in
                            NC = {ArgsInClosure ArgList xs closure E}
                            {Push SStack S NC}
                        end
                    end
                [] equivalence(_) then
                raise 'unbound proc' end
                else raise 'variable is not a procedure' end
                end
            end
            end
    end
end
