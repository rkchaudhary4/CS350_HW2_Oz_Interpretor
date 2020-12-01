\insert 'Unify.oz'
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
            case SortedX of nil then raise 'error occured' end
            [] [literal(_) H1]|T1 then
                Et = {Adjoin E environment(H:{AddKeyToSAS})}
                {Unify ident(H) H1 Et}
                {Unifier T1 T Et Enew}
            else raise 'error occured' end
            end
    end
end

fun {GetRecordKeys Record}
	case Record
	of nil then nil
	[] H|T then H.1 | {GetRecordKeys T}
	end
end

fun {RecordValues Record}
    case Record
    of nil then nil
    [] H|T then H.2.1 | {RecordValues T}
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
                else raise 'error' end
                end
            else raise 'error' end
        end
        end
    }
end

fun {NotUnique List}
    case List of nil then false
    [] H|T then if {Member H T} then true else {NotUnique T} end
    end
end

fun {ArgsInClosure ArgList Xs Closure E}
    case ArgList
    of nil then Closure
    [] ident(H) | T then
        case Xs
        of nil then raise 'wrong arguments to procedure' end
        [] ident(H1) | T1 then
            {ArgsInClosure T T1 {Adjoin Closure environment(H:E.H1)} E}
        [] H1 | T1 then
            local A in
                A = {AddKeyToSAS}
                {BindValueToKeyInSAS A H1}
                {ArgsInClosure T T1 {Adjoin Closure environment(H:A)} E}
            end
        end 
    end
end

fun {MakeEnvironment Args E}
	case Args of X|Xs then
		if X == nothing then {MakeEnvironment Xs E}
		else {Adjoin environment(X:E.X) {MakeEnvironment Xs E}}
		end
	else environment() end
end

fun {CalcClosure S E}
    case S of [localvar ident(X) S1] then {Record.subtract {CalcClosure S1 {Adjoin environment(X:0) E}}X} 
    [] [bind ident(X) ident(Y)] then environment(X:E.X Y:E.Y)
    [] [bind X1 Y1] then
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
            if V.1 == record then
                {Adjoin environment(X:E.X) {MakeEnvironment {Map {RecordValues V.2.2} fun {$ A} case A of ident(X) then X else nothing end end} E}}
            else environment(X:E.X) 
            end
        end
    [] [apply ident(X) Args] then
        {Adjoin environment(X:E.X) {MakeEnvironment Args E}}
    [] [match ident(X) P1 S1 S2] then
        local Vars = {RecordValues P1.2.2} in
            {Adjoin {Adjoin environment(X:E.X) {Record.subtractList {CalcClosure S1 {AdjoinList E {Map Vars fun {$ A} A#0 end}}} Vars}} {CalcClosure S2 E}}
        end
    [] S1|S2 then {Adjoin {CalcClosure S1 E} {CalcClosure S2 E}}
    else environment(nil)
    end
end