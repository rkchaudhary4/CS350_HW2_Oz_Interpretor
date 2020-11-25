declare
proc {MatchBind ValOfX P E Match En}
    if {Length ValOfX.2.2.1} \= {Length P.2.2.1} then Match = false
    else if ValOfX.2.1 \= P.2.1 then Match = false
    else
        SortedX SortedP in
            SortedX = {SortRecord ValOfX.2.2.1}
            SortedP = {SortRecord SortedP.2.2.1}
            if {NotUnique {GetRecordKeys SortedX}} then Match = false
            elseif {NotUnique {GetRecordKeys SortedP}} then Match = false
            elseif {GetRecordKeys SortedP} \= {GetRecordKeys SortedX} then Match = false
            else
                {Unifier SortedX SortedP E En}
                Match = true
            end
        end 
        end
end

proc {Unifier SortedX SortedP E Enew}
    Et in
        case SortedP of nil then Enew = E
        [] [literal(_) ident(H)]|T then
            case SortedX of nil then raise error() end
            [] [literal(_) H1]|T1 then
                Et = {Adjoin E environment(H:{AddKeyToSAS})}
                {Unify ident(H) H1 Et}
                {Unifier T1 T Et Enew}
            else raise error() end
            end
    end
end

fun {GetRecordKeys Record}
	case Record
	of nil then nil
	[] H|T then H.1 | {GetRecordKeys T}
	end
end

fun {SortRecord R}
    {Sort R
        fun {$ R1 R2}
            case R1 of literal(F1)|T then
                case R2 of literal(F2)|T1 then
                    if {IsNumber F1} == {IsNumber F2} then F1 < F2
                    else {IsNumber F1}
                    end
                else raise error() end
                end
            else raise error() end
        end
        end
    }
end

fun {NotUnique List}
    case List of nil then false
    [] H|T then if {Member H T} then true else {NotUnique T} end
    end
end

fun {ArgsInClosure ArgList xs closure E}
    case ArgList
    of nil then closure
    [] ident(H) | T then
        case xs
        of nil then raise 'wrong arguments to procedure' end
        [] ident(H1) | T1 then
            {ArgsInClosure T T1 {Adjoin closure environment(H:E.H1)} E}
        [] H1 | T1 then
            local A in
                A = {AddKeyToSAS}
                {BindValueToKeyInSAS A H1}
                {ArgsInClosure T T1 {Adjoin closure environment(H:A)} E}
            end
        end 
    end
end