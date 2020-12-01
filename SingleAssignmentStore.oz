declare SAS RetrieveFromSAS BindRefToKeyInSAS  BindValueToKeyInSAS AddKeyToSAS Count
SAS ={Dictionary.new}
Count = {NewCell 0}
fun {RetrieveFromSAS X}
   if {Dictionary.member SAS X}
    then
        local V = {Dictionary.get SAS X} in
	            case V of unbound then equivalence(X)
	                [] reference(Z) then {RetrieveFromSAS Z}
	                else V end
            end
    else raise 'Key missing during assigning' end
    end
end

proc {BindValueToKeyInSAS X Val}
   case {Dictionary.condGet SAS X unbound} of
    unbound then {Dictionary.put SAS X Val}
    [] reference(Z) then {BindValueToKeyInSAS Z Val}
    [] Z then raise 'keyAlreadyAssigned' end
   else skip
   end
end

proc {BindRefToKeyInSAS X Ref}
   case {Dictionary.condGet SAS X unbound} of
      unbound then {Dictionary.put SAS X reference(Ref)}
   [] reference(Z) then {BindRefToKeyInSAS Z Ref}
   else
    skip
   end
end

fun {AddKeyToSAS}
   local Key = @Count in
      {Dictionary.put SAS Key unbound}
      Count := @Count + 1
      Key
   end
end