declare SAS RetrieveFromSAS BindRefToKeyInSAS  BindValueToKeyInSAS

SAS ={Dictionary.new}

fun {RetrieveFromSAS X}
   if {Dictionary.member SAS X}
    then
        local V = {Dictionary.get SAS X} in
	            case V of unbound then equivalence(X)
	                [] reference(Z) then {RetrieveFromSAS Z}
	                else V end
            end
    else raise keyMissing(X) end
    end
end

declare
proc {BindValueToKeyInSAS X Val}
   case {Dictionary.condGet SAS X unbound} of
    unbound then {Dictionary.put SAS X Val}
    [] reference(Z) then {BindValueToKeyInSAS Z Val}
    [] Z then raise keyAlreadyAssigned(X) end
   else skip
   end
end

declare
proc {BindRefToKeyInSAS X Ref}
   case {Dictionary.condGet SAS X unbound} of
      unbound then {Dictionary.put SAS X reference(Ref)}
   [] reference(Z) then {BindRefToKeyInSAS Z Ref}
   else
    skip
   end
end

proc {AddKeyToSAS Key}
    {Dictionary.put SAS Key unbound}
end