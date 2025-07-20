from z3 import *

def main():
    # Define the Z3 integer variables for day and start time
    d = Int('d')
    s = Int('s')
    
    # Constraints for day (0,1,2) and start time (0 to 420 minutes from 9:00)
    constraints = [d >= 0, d <= 2, s >= 0, s <= 420]
    
    # Roy's busy intervals in minutes from 9:00 for each day
    busy = {
        0: [(60, 150), (180, 240), (300, 330), (360, 480)],   # Monday
        1: [(90, 150), (180, 330), (360, 390), (420, 480)],   # Tuesday
        2: [(30, 150), (210, 300), (330, 390), (450, 480)]    # Wednesday
    }
    
    # Add constraints to avoid overlapping with Roy's busy times
    for day, intervals in busy.items():
        for (b_start, b_end) in intervals:
            constraints.append(Or(d != day, s + 60 <= b_start, s >= b_end))
    
    # Set up the optimizer to minimize (d*1000 + s) for earliest availability
    opt = Optimize()
    opt.add(constraints)
    objective = d * 1000 + s
    opt.minimize(objective)
    
    # Check for a solution and print results
    if opt.check() == sat:
        m = opt.model()
        day_val = m[d].as_long()
        s_val = m[s].as_long()
        
        # Convert day index to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Calculate start time (HH:MM)
        start_hour = 9 + s_val // 60
        start_min = s_val % 60
        start_time = f"{start_hour}:{start_min:02d}"
        
        # Calculate end time (start time + 60 minutes)
        end_total_min = s_val + 60
        end_hour = 9 + end_total_min // 60
        end_min = end_total_min % 60
        end_time = f"{end_hour}:{end_min:02d}"
        
        # Output the solution
        print(day_str)
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()