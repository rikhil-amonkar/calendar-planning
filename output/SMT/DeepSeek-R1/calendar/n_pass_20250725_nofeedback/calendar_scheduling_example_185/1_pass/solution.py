from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Start time in minutes from midnight
    S = Int('S')
    
    # Work hours: 9:00 (540) to 17:00 (1020), meeting duration 30 minutes
    s.add(S >= 540)        # Meeting must start at or after 9:00
    s.add(S <= 990)        # Meeting must start by 16:30 to end by 17:00
    
    # Megan's preference: avoid meetings before 10:00 (600 minutes)
    s.add(S >= 600)
    
    # Busy intervals for each participant (start, end) in minutes
    busy_times = {
        'Kimberly': [(600, 630), (660, 720), (960, 990)],
        'Marie': [(600, 660), (690, 900), (960, 990)],
        'Diana': [(570, 600), (630, 870), (930, 1020)],
        'Megan': []
    }
    
    # Add constraints for each busy interval
    for person, intervals in busy_times.items():
        for (b_start, b_end) in intervals:
            s.add(Or(S >= b_end, S + 30 <= b_start))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[S].as_long()
        # Convert start time to HH:MM format
        hour = start_min // 60
        minute = start_min % 60
        start_time = f"{hour:02d}:{minute:02d}"
        # Calculate end time
        end_min = start_min + 30
        hour_end = end_min // 60
        minute_end = end_min % 60
        end_time = f"{hour_end:02d}:{minute_end:02d}"
        
        # Format the solution
        solution = "SOLUTION:\n" + \
                   "Day: Monday\n" + \
                   f"Start Time: {start_time}\n" + \
                   f"End Time: {end_time}"
        print(solution)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()