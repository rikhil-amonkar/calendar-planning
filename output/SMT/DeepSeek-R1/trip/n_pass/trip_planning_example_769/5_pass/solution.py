from z3 import *

def solve_planning():
    # Constants
    num_rooms = 2
    horizon = 2  # Two steps: unlock and move

    # State variables
    robot = [Int(f'robot_{i}') for i in range(horizon + 1)]
    key = [Int(f'key_{i}') for i in range(horizon + 1)]
    door_locked = [Bool(f'door_locked_{i}') for i in range(horizon + 1)]
    actions = [Int(f'action_{i}') for i in range(horizon)]

    # Solver
    s = Solver()

    # Initial state constraints
    s.add(robot[0] == 0)   # Robot starts in room0
    s.add(key[0] == 1)      # Key starts in room1
    s.add(door_locked[0] == True)  # Door initially locked

    # State variable domains
    for t in range(horizon + 1):
        s.add(Or(robot[t] == 0, robot[t] == 1))
        s.add(Or(key[t] == 0, key[t] == 1))

    # Goal constraint
    s.add(robot[horizon] == 1)  # Robot must be in room1 at the end

    # Action definitions: 
    # 0 = unlock_door(room0, room1)
    # 1 = move(room0, room1)
    # 2 = move(room1, room0)
    for t in range(horizon):
        action = actions[t]
        
        # Unlock door action
        unlock = And(action == 0,
                     # Robot and key must be in the same room
                     robot[t] == key[t],
                     door_locked[t] == True,
                     # After unlock: robot stays, key stays, door unlocked
                     robot[t+1] == robot[t],
                     key[t+1] == key[t],
                     door_locked[t+1] == False)
        
        # Move from room0 to room1 action
        move01 = And(action == 1,
                     robot[t] == 0,
                     door_locked[t] == False,
                     # Robot moves to room1
                     robot[t+1] == 1,
                     # Key moves with robot if they're together
                     key[t+1] == If(key[t] == robot[t], 1, key[t]),
                     door_locked[t+1] == door_locked[t])
        
        # Move from room1 to room0 action
        move10 = And(action == 2,
                     robot[t] == 1,
                     door_locked[t] == False,
                     # Robot moves to room0
                     robot[t+1] == 0,
                     # Key moves with robot if they're together
                     key[t+1] == If(key[t] == robot[t], 0, key[t]),
                     door_locked[t+1] == door_locked[t])
        
        # Only allow defined actions
        s.add(Or(unlock, move01, move10))
        s.add(action >= 0, action <= 2)

    # Solve and output the plan
    if s.check() == sat:
        m = s.model()
        plan = []
        for t in range(horizon):
            a = m[actions[t]].as_long()
            if a == 0:
                plan.append("unlock_door(room0, room1)")
            elif a == 1:
                plan.append("move(room0, room1)")
            elif a == 2:
                plan.append("move(room1, room0)")
        print("Plan found:")
        for step, action in enumerate(plan):
            print(f"Step {step}: {action}")
    else:
        print("No plan found")

solve_planning()