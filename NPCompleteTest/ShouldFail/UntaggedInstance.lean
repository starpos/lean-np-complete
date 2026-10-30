module

meta import NPComplete.Meta.ApiLayer
meta import NPComplete.Meta.ApiLayerCheck

@[expose] public section

namespace NPComplete.Test

@[stable_api] inductive InstanceFixture where
  | value

instance arbitraryInstanceName : Repr InstanceFixture where
  reprPrec _ _ := "fixture"

end NPComplete.Test

#check_api_instances
