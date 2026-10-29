module

public import NPComplete
public import NPComplete.Test.Witnesses
meta import NPComplete.Meta.ApiLayerCheck

/-!
# Layering check of the tagged API

Runs `#check_api_layers` over every `stable_api` and `construction_api` declaration reachable from
`NPComplete` and from the modules collected in `Witnesses.lean`. A violation is an error, so a
statement that starts to mention an internal declaration breaks `lake build NPComplete.Extra`.

`#check_api_umbrella` additionally requires every such declaration to be defined in a module that
`import NPComplete` reaches, since the umbrella is the only entry point promised to clients.
-/

#check_api_layers

#check_api_umbrella
