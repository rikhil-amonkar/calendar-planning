from z3 import *

def main():
    # Create solver
    opt = Optimize()
    
    # Day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    day = Int('day')
    start = Int('start')  # in minutes from 00:00
    
    # Constraints for day and start time
    opt.add(day >= 0, day <= 3)
    opt.add(start >= 540)   # 9:00 in minutes (9*60)
    opt.add(start <= 960)   # 16:00 to ensure meeting ends by 17:00 (start+60 <= 1020)
    
    # Megan's busy intervals (half-open [start, end))
    megan_busy = {
        0: [(780, 810), (840, 930)],
        1: [(540, 570), (720, 750), (960, 1020)],
        2: [(570, 600), (630, 690), (750, 840), (960, 990)],
        3: [(810, 870), (900, 930)]
    }
    
    # Daniel's busy intervals (half-open [start, end))
    daniel_busy = {
        0: [(600, 690), (750, 900)],
        1: [(540, 600), (630, 1020)],
        2: [(540, 600), (630, 690), (720, 1020)],
        3: [(540, 720), (750, 870), (900, 930), (960, 1020)]
    }
    
    # Function to add busy constraints for a person
    def add_busy_constraints(person_busy):
        for d, intervals in person_busy.items():
            constraints = []
            for b, e in intervals:
                constraints.append(Or(start + 60 <= b, start >= e))
            opt.add(Implies(day == d, And(constraints)))
    
    # Add constraints for Megan and Daniel
    add_busy_constraints(megan_busy)
    add_busy_constraints(daniel_busy)
    
    # Minimize total minutes from start of week (Monday 00:00)
    total_minutes = day * 1440 + start  # 1440 minutes in a day
    opt.minimize(total_minutes)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        s_val = m[start].as_long()
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[d_val]
        # Format start time
        hour = s_val // 60
        minute = s_val % 60
        start_time = f"{hour:02d}:{minute:02d}"
        # Calculate end time
        end_val = s_val + 60
        end_hour = end_val // 60
        end_minute = end_val % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        # Print solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()