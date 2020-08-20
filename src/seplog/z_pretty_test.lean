import seplog.z_pretty
import seplog.d_context_test

meta def f: File := structs_to_file "main"
                    [⟨_, Vndkdep⟩, ⟨_,MutatorSet⟩, ⟨_,Mod⟩]
                    --[⟨_, LL⟩]
#eval f.write "/tmp"