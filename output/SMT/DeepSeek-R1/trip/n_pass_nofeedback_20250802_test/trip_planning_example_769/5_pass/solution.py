from z3 import *

def main():
    blocks = ['A', 'B', 'C']
    objects = ['A', 'B', 'C', 'Table']
    num_steps = 4  # Allow 4 actions

    s = Solver()
    
    # State variables: on[block, object, time]
    on = {}
    for b in blocks:
        for o in objects:
            for t in range(num_steps + 1):
                on[(b, o, t)] = Bool('on_{}_{}_{}'.format(b, o, t))
    
    # Action variables
    move_block = [String('move_block_{}'.format(t)) for t in range(num_steps)]
    move_to = [String('move_to_{}'.format(t)) for t in range(num_steps)]
    
    # Each block is on exactly one object at each time
    for t in range(num_steps + 1):
        for b in blocks:
            s.add(Sum([If(on[(b, o, t)], 1, 0) for o in objects]) == 1)
    
    # Action constraints
    for t in range(num_steps):
        # Action must be either "none" or a valid block
        s.add(Or(move_block[t] == "none", 
                 Or([move_block[t] == b for b in blocks])))
        
        # Destination must be valid when moving
        move_cond = move_block[t] != "none"
        s.add(Implies(move_cond, Or([move_to[t] == o for o in objects])))
        s.add(Implies(move_cond, move_to[t] != move_block[t]))
        
        # Preconditions: clear moving block and clear destination (if not Table)
        for b_val in blocks:
            for d_val in objects:
                if b_val == d_val:
                    continue
                # Moving b_val to d_val?
                action_match = And(move_block[t] == b_val, move_to[t] == d_val)
                
                # Clear moving block: nothing on it
                clear_b = And([Not(on[(c, b_val, t)]) for c in blocks])
                
                # Clear destination if it's a block
                clear_d = And([Not(on[(c, d_val, t)]) for c in blocks]) if d_val != "Table" else True
                
                s.add(Implies(action_match, And(clear_b, clear_d)))
        
        # State transitions
        for b in blocks:
            for o in objects:
                # If this block is being moved
                moved = And(move_block[t] == b, 
                            on[(b, o, t+1)] == (move_to[t] == o))
                
                # If not being moved, maintain position
                not_moved = And(move_block[t] != b, 
                                on[(b, o, t+1)] == on[(b, o, t)])
                
                s.add(Or(moved, not_moved))
    
    # Initial state
    s.add(on[('A', 'B', 0)])
    s.add(on[('B', 'C', 0)])
    s.add(on[('C', 'Table', 0)])
    
    # Clear initial positions
    s.add(Not(on[('A', 'A', 0)]))
    s.add(Not(on[('B', 'B', 0)]))
    s.add(Not(on[('C', 'C', 0)]))
    s.add(Not(on[('A', 'Table', 0)]))
    s.add(Not(on[('A', 'C', 0)]))
    s.add(Not(on[('B', 'Table', 0)]))
    s.add(Not(on[('B', 'A', 0)]))
    s.add(Not(on[('C', 'A', 0)]))
    s.add(Not(on[('C', 'B', 0)]))
    
    # Goal state
    s.add(on[('A', 'B', num_steps)])
    s.add(on[('B', 'Table', num_steps)])
    s.add(on[('C', 'A', num_steps)])
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        print("Plan found:")
        for t in range(num_steps):
            block = m.eval(move_block[t])
            if block.as_string() != "none":
                dest = m.eval(move_to[t])
                # Find current location
                for o in objects:
                    if m.eval(on[(block.as_string(), o, t)]):
                        src = o
                        break
                print(f"Step {t}: Move {block} from {src} to {dest}")
    else:
        print("No plan found")

if __name__ == '__main__':
    main()