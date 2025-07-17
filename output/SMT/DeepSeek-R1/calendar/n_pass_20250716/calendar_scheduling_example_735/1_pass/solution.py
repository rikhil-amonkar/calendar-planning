from z3 import *

def main():
    # Blocked times in minutes from 9:00 for Ronald and Amber for each day
    ronald_blocked = {
        0: [(90, 120), (180, 210), (390, 420)],  # Monday
        1: [(0, 30), (180, 210), (390, 450)],     # Tuesday
        2: [(30, 90), (120, 180), (210, 240), (270, 300), (450, 480)]  # Wednesday
    }
    
    amber_blocked = {
        0: [(0, 30), (60, 90), (150, 180), (210, 300), (330, 360), (390, 480)],  # Monday
        1: [(0, 30), (60, 150), (180, 210), (270, 390), (450, 480)],  # Tuesday
        2: [(0, 30), (60, 90), (120, 270), (360, 390)]  # Wednesday
    }
    
    # Create Z3 variables
    day = Int('day')
    start = Int('start')
    
    # Constraints
    constraints = []
    constraints.append(day >= 0)
    constraints.append(day <= 2)
    constraints.append(start >= 0)
    constraints.append(start <= 450)  # 450 minutes = 16:30 (since meeting is 30 min)
    
    # Add constraints for avoiding blocked times
    for d in [0, 1, 2]:
        for (s, e) in ronald_blocked[d]:
            constraints.append(Implies(day == d, Or(start + 30 <= s, start >= e)))
        for (s, e) in amber_blocked[d]:
            constraints.append(Implies(day == d, Or(start + 30 <= s, start >= e)))
    
    # Create optimizer and minimize the objective (earliest time)
    opt = Optimize()
    opt.add(constraints)
    objective = day * 480 + start
    opt.minimize(objective)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Convert day value to day name
        day_names = ['Monday', 'Tuesday', 'Wednesday']
        day_str = day_names[d_val]
        
        # Calculate start time
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time (30 minutes after start)
        end_val = start_val + 30
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        # Print the solution
        print(day_str, start_time, end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()