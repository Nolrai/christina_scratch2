import Lake
open Lake DSL

package «christina_scratch2» where
  -- add package configuration options here

lean_lib «ChristinaScratch2» where
  -- add library configuration options here

@[default_target]
lean_exe «christina_scratch2» where
  root := `Main
