from z3 import *

def main():
    # Define the variables
    day = Int('day')
    s = Int('s')  # start time in minutes after 9:00

    # Constraints for day and s
    constraints = [day >= 0, day <= 2, s >= 0, s <= 450]  # s <= 450 ensures meeting ends by 17:00

    # Busy intervals: each interval is (start_minute, end_minute) and represents [start, end)
    busy_intervals = {
        0: [(0, 60), (90, 180), (210, 330), (360, 420), (450, 480)],  # Monday (Ruth's busy times)
        1: [(0, 30), (330, 360), (0, 480)],  # Tuesday (Tyler's and Ruth's busy times)
        2: [(90, 120), (210, 240), (270, 300), (450, 480), (0, 480)]  # Wednesday (Tyler's and Ruth's busy times)
    }

    # Monday constraints: Tyler's preference (s >= 420) and avoid busy intervals
    monday_constraints = [s >= 420]
    for b, e in busy_intervals[0]:
        monday_constraints.append(Or(s + 30 <= b, s >= e))
    
    # Tuesday constraints: avoid busy intervals
    tuesday_constraints = []
    for b, e in busy_intervals[1]:
        tuesday_constraints.append(Or(s + 30 <= b, s >= e))
    
    # Wednesday constraints: avoid busy intervals
    wednesday_constraints = []
    for b, e in busy_intervals[2]:
        wednesday_constraints.append(Or(s + 30 <= b, s >= e))
    
    # Add implications for each day
    constraints.append(Implies(day == 0, And(monday_constraints)))
    constraints.append(Implies(day == 1, And(tuesday_constraints)))
    constraints.append(Implies(day == 2, And(wednesday_constraints)))
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        s_val = model[s].as_long()
        
        # Map day value to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Calculate start time (HH:MM)
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = s_val + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        # Output the solution
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()