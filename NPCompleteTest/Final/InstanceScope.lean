module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.ApiLayerCheck

@[expose] public section

namespace NPComplete.Test

@[stable_api] inductive ScopedInstanceFixture where
  | value

section

local instance localFixture : Inhabited ScopedInstanceFixture := ⟨.value⟩

#guard_msgs in
#check_api_instances

end

end NPComplete.Test
