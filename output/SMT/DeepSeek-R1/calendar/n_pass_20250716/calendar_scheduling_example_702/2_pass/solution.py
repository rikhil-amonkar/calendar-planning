from z3 import *

def main():
    # Corrected busy intervals in minutes from 9:00
    robert_busy = {
        0: [(120, 150), (300, 330), (390, 420)],   # Monday
        1: [(90, 120), (360, 390)],                # Tuesday
        2: [(60, 120), (150, 180), (210, 240), (270, 300), (360, 390), (420, 450)]  # Wednesday
    }
    
    ralph_busy = {
        0: [(60, 270), (300, 330), (360, 480)],    # Monday
        1: [(0, 30), (60, 90), (120, 150), (180, 240), (300, 390), (420, 480)], # Tuesday
        2: [(90, 120), (150, 180), (240, 330), (450, 480)]   # Wednesday
    }
    
    # Create Z3 variables
    d = Int('d')
    s = Int('s')
    
    solver = Optimize()
    
    # Exclude Monday (0) due to conflict and preference
    solver.add(Or(d == 1, d == 2))  # Only consider Tuesday (1) or Wednesday (2)
    # Start time must be between 0 and 450 minutes (inclusive)
    solver.add(s >= 0)
    solver.add(s <= 450)
    
    # Non-overlap constraints per day
    tuesday_intervals = robert_busy[1] + ralph_busy[1]
    wednesday_intervals = robert_busy[2] + ralph_busy[2]
    
    # Ensure no overlap with busy intervals for the selected day
    solver.add(Or(
        And(d == 1, And([Or(s >= end, s + 30 <= start) for (start, end) in tuesday_intervals])),
        And(d == 2, And([Or(s >= end, s + 30 <= start) for (start, end) in wednesday_intervals]))
    ))
    
    # Minimize total minutes from Monday 9:00 (earliest availability)
    total_minutes = d * 1440 + s  # 1440 minutes = 24 hours
    solver.minimize(total_minutes)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        d_val = model[d].as_long()
        s_val = model[s].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        # Calculate start time (HH:MM)
        start_hour = 9 + s_val // 60
        start_min = s_val % 60
        start_time = f"{start_hour}:{start_min:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = s_val + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour}:{end_min:02d}"
        
        print(f"Day: {day_str}")
        print(f"Start: {start_time}")
        print(f"End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()