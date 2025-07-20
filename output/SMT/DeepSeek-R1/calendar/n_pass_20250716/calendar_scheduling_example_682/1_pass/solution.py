from z3 import *

def main():
    # Create a solver
    s = Int('s')
    solver = Solver()
    
    # Convert time to minutes: 9:00 = 540, 11:00 = 660
    work_start = 540
    meeting_end_limit = 660
    meeting_duration = 30
    
    # Time constraints: within work hours and meeting ends by 11:00
    solver.add(s >= work_start)
    solver.add(s + meeting_duration <= meeting_end_limit)
    
    # Amanda's busy intervals on Tuesday in minutes: [540, 570) and [600, 630)
    amanda_intervals = [(540, 570), (600, 630)]
    for start, end in amanda_intervals:
        # Non-overlap condition: meeting ends before the interval starts or starts after the interval ends
        solver.add(Or(s + meeting_duration <= start, s >= end))
    
    # Nathan's busy interval on Tuesday: [540, 630)
    nathan_interval_start = 540
    nathan_interval_end = 630
    solver.add(Or(s + meeting_duration <= nathan_interval_start, s >= nathan_interval_end))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        
        # Convert start time to hours and minutes
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        day = "Tuesday"
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        print(f"{day} {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()