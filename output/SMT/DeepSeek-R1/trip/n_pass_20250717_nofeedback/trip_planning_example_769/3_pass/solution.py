from z3 import *

def solve_planning():
    # Constants
    num_rooms = 2
    horizon = 3  # Three actions needed

    # State variables
    robot = [Int(f'robot_{i}') for i in range(horizon + 1)]
    key = [Int(f'key_{i}') for i in range(horizon + 1)]
    door_locked = [Bool(f'door_locked_{i}') for i in range(horizon + 1)]
    actions = [Int(f'action_{i}') for i in range(horizon)]  # Actions at steps 0,1,2

    # Solver
    s = Solver()

    # Initial state constraints (corrected to match problem)
    s.add(robot[0] == 0)   # Robot starts in room0
    s.add(key[0] == 1)      # Key starts in room1 (as specified)
    s.add(door_locked[0] == True)  # Door initially locked

    # Goal constraint
    s.add(robot[horizon] == 1)  # Robot must be in room1 at the end

    # State variable domains
    for t in range(horizon + 1):
        s.add(Or(robot[t] == 0, robot[t] == 1))
        s.add(Or(key[t] == 0, key[t] == 1))

    # Action definitions: 
    # 0=no-op, 1=unlock, 2=move01, 3=move10, 
    # 4=pass_key_to_room0, 5=pass_key_to_room1
    for t in range(horizon):
        action = actions[t]
        
        # No-op action
        noop = And(action == 0,
                   robot[t+1] == robot[t],
                   key[t+1] == key[t],
                   door_locked[t+1] == door_locked[t])
        
        # Unlock action
        unlock = And(action == 1,
                     robot[t] == key[t],  # Robot and key in same room
                     door_locked[t] == True,
                     robot[t+1] == robot[t],
                     key[t+1] == key[t],
                     door_locked[t+1] == False)
        
        # Move from room0 to room1
        move01 = And(action == 2,
                     robot[t] == 0,
                     door_locked[t] == False,
                     robot[t+1] == 1,
                     key[t+1] == key[t],
                     door_locked[t+1] == door_locked[t])
        
        # Move from room1 to room0
        move10 = And(action == 3,
                     robot[t] == 1,
                     door_locked[t] == False,
                     robot[t+1] == 0,
                     key[t+1] == key[t],
                     door_locked[t+1] == door_locked[t])
        
        # Pass key from room1 to room0
        pass_to0 = And(action == 4,
                       key[t] == 1,
                       robot[t] == 0,
                       key[t+1] == 0,
                       robot[t+1] == robot[t],
                       door_locked[t+1] == door_locked[t])
        
        # Pass key from room0 to room1
        pass_to1 = And(action == 5,
                       key[t] == 0,
                       robot[t] == 1,
                       key[t+1] == 1,
                       robot[t+1] == robot[t],
                       door_locked[t+1] == door_locked[t])
        
        # Action selection constraints
        s.add(Or(noop, unlock, move01, move10, pass_to0, pass_to1))
        
        # Ensure action value is valid
        s.add(action >= 0, action <= 5)

    # Solve and output the plan
    if s.check() == sat:
        m = s.model()
        plan = []
        for t in range(horizon):
            a = m[actions[t]].as_long()
            if a == 0:
                plan.append("no-op")
            elif a == 1:
                plan.append("unlock_door")
            elif a == 2:
                plan.append("move(room0, room1)")
            elif a == 3:
                plan.append("move(room1, room0)")
            elif a == 4:
                plan.append("pass_key(room1->room0)")
            elif a == 5:
                plan.append("pass_key(room0->room1)")
        print("Plan found:")
        for step, action in enumerate(plan):
            print(f"Step {step}: {action}")
    else:
        print("No plan found")

solve_planning()