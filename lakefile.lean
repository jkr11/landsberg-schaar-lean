import Lake
open Lake DSL

package "landsberg-schaar" where
  -- add package configuration options here

lean_lib «LandsbergSchaar» where
  -- add library configuration options here

@[default_target]
lean_exe "landsberg-schaar" where
  root := `Main
