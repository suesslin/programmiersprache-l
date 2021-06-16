module AbstractMachine where
    import Parser (Tree(..))

    type B = Bool    -- Backtrack
    type T = Int
    type C = Int
    type R = Int
    type P = Int     -- Next command
    -- type I = Int. -- Current command

    type AdressRegs = (T, C, R, P)
    data StackElement = Integer | String
    type Stack = [Maybe StackElement]

    -- Haupt-Instruktionstyp: vmtl. selbe Signatur nur mit I dazu

    -- push :: (AdressRegs, Stack, B) -> (AdressRegs, Stack, B)
    -- push (regs, stack, b) = ((), stack, drop 3 stack /= )

    -- unify :: (AdressRegs, Stack, B) -> [(AdressRegs, Stack, B)]
    -- unify () = (regs, stack, b) = ((), stack, drop 3 stack /= ) 

    -- call :: [(AdressRegs, Stack, B)] -> [(AdressRegs, Stack, B)]
    -- call = undefined 

    -- return :: [(AdressRegs, Stack, B)] -> [(AdressRegs, Stack, B)]
    -- return = undefined

    -- backtrack :: [(AdressRegs, Stack, B)] -> [(AdressRegs, Stack, B)]
    -- backtrack = undefined

    -- üb :: Tree -> []