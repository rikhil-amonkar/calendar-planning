from z3 import *

def solve_planning():
    # Constants
    num_rooms = 2
    horizon = 2  # Two actions: unlock and move

    # State variables
    robot = [Int(f'robot_{i}') for i in range(horizon + 1)]
    key = [Int(f'key_{i}') for i in range(horizon + 1)]
    door_locked = [Bool(f'door_locked_{i}') for i in range(horizon + 1)]
    actions = [Int(f'action_{i}') for i in range(horizon)]  # Actions at step 0 and 1

    # Solver
    s = Solver()

    # Initial state constraints
    s.add(robot[0] == 0)  # Robot starts in room0
    s.add(key[0] == 0)    # Key starts in room0 (adjusted from room1)
    s.add(door_locked[0] == True)  # Door initially locked

    # Goal constraint
    s.add(robot[horizon] == 1)  # Robot must be in room1 at the end

    # Action definitions: 0=no-op, 1=unlock, 2=move01, 3=move10
    for t in range(horizon):
        action = actions[t]
        # Preconditions and effects for each action
        # Unlock action
        unlock_pre = And(robot[t] == key[t], door_locked[t] == True)
        unlock_eff = And(robot[t+1] == robot[t], key[t+1] == key[t], door_locked[t+1] == False)
        
        # Move from room0 to room1
        move01_pre = And(robot[t] == 0, door_locked[t] == False)
        move01_eff = And(robot[t+1] == 1, key[t+1] == If(key[t] == 0, 1, key[t]), door_locked[t+1] == door_locked[t])
        
        # Move from room1 to room0
        move10_pre = And(robot[t] == 1, door_locked[t] == False)
        move10_eff = And(robot[t+1] == 0, key[t+1] == If(key[t] == 1, 0, key[t]), door_locked[t+1] == door_locked[t])
        
        # No-op action
        noop_eff = And(robot[t+1] == robot[t], key[t+1] == key[t], door_locked[t+1] == door_locked[t])
        
        # Action selection constraints
        s.add(Or(
            And(action == 0, noop_eff),  # No-op
            And(action == 1, unlock_pre, unlock_eff),  # Unlock
            And(action == 2, move01_pre, move01_eff),  # Move01
            And(action == 3, move10_pre, move10_eff)   # Move10
        ))
        
        # Ensure action value is valid
        s.add(action >= 0, action <= 3)

    # Solve and output the plan
    if s.check() == sat:
        m = s.model()
        plan = []
        for t in range(horizon):
            a = m[actions[t]].as_long()
            if a == 0:
                plan.append("no-op")
            elif a == 1:
                plan.append("unlock_door(room0, room1)")
            elif a == 2:
                plan.append("move(room0, room1)")
            elif a == 3:
                plan.append("move(room1, room0)")
        print("Plan found:")
        for step, action in enumerate(plan):
            print(f"Step {step}: {action}")
    else:
        print("No plan found")

solve_planning()