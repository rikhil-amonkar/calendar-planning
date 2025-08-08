from z3 import *

def main():
    blocks = ['A', 'B', 'C']
    objects = ['A', 'B', 'C', 'Table']
    num_steps = 4  # Number of actions allowed (time steps 0 to 4)

    # Create the solver
    s = Solver()

    # Create on predicates: on[block, object, time]
    on = {}
    for b in blocks:
        for o in objects:
            for t in range(num_steps + 1):
                on[(b, o, t)] = Bool('on_{}_{}_{}'.format(b, o, t))

    # Action variables for each time step
    move_b = [String('move_b_{}'.format(i)) for i in range(num_steps)]
    move_to = [String('move_to_{}'.format(i)) for i in range(num_steps)]

    # Uniqueness constraint: each block is on exactly one object at each time
    for t in range(num_steps + 1):
        for b in blocks:
            s.add(Sum([If(on[(b, o, t)], 1, 0) for o in objects]) == 1)

    # Action constraints for each time step
    for t in range(num_steps):
        # Move block must be "none" or a valid block
        s.add(Or([move_b[t] == b for b in blocks] + [move_b[t] == "none"]))
        
        # If moving, destination must be a valid object and not the block itself
        s.add(If(move_b[t] != "none",
                 Or([move_to[t] == o for o in objects if o != move_b[t]]),
                 True))
        
        # Precondition: cannot move to itself
        s.add(If(move_b[t] != "none", move_to[t] != move_b[t], True))
        
        # Preconditions for move: clear moving block and clear destination (if not table)
        for b_val in blocks:
            for d_val in objects:
                if b_val == d_val:
                    continue
                cond = And(move_b[t] == b_val, move_to[t] == d_val)
                # Clear(b_val, t): no block on b_val
                clear_b = And([Not(on[(c, b_val, t)]) for c in blocks])
                # Clear(d_val, t) if destination is not table
                clear_d = And([Not(on[(c, d_val, t)]) for c in blocks]) if d_val != "Table" else True
                s.add(Implies(cond, And(clear_b, clear_d)))
        
        # Effect on state: update positions
        for b in blocks:
            for o in objects:
                # If current block is moved, set its new position
                moved = And(move_b[t] == b, on[(b, o, t+1)] == (o == move_to[t]))
                # If not moved, keep position from previous time
                not_moved = And(move_b[t] != b, on[(b, o, t+1)] == on[(b, o, t)])
                s.add(If(move_b[t] == b, moved, not_moved))

    # Initial state: A on B, B on C, C on table
    s.add(on[('A', 'B', 0)])
    s.add(on[('B', 'C', 0)])
    s.add(on[('C', 'Table', 0)])
    
    # Goal state: A on B, B on table, C on A
    s.add(on[('A', 'B', num_steps)])
    s.add(on[('B', 'Table', num_steps)])
    s.add(on[('C', 'A', num_steps)])

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        plan = []
        for t in range(num_steps):
            if m.eval(move_b[t]).as_string() != "none":
                action = "Move({} from {} to {})".format(
                    m.eval(move_b[t]),
                    [o for o in objects if m.eval(on[(m.eval(move_b[t]), o, t)])],
                    m.eval(move_to[t])
                )
                plan.append((t, action))
        print("Plan found:")
        for step, action in plan:
            print("Step {}: {}".format(step, action))
    else:
        print("No plan found")

if __name__ == '__main__':
    main()