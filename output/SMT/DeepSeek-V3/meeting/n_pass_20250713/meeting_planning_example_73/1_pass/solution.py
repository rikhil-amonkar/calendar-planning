from z3 import *

def solve_meeting_schedule():
    # Initialize the solver
    s = Solver()
    
    # Convert all times to minutes since midnight for easier arithmetic
    # Barbara's availability: 7:15 AM to 10:00 PM
    barbara_start = 7 * 60 + 15  # 7:15 AM in minutes
    barbara_end = 22 * 60        # 10:00 PM in minutes
    
    # You arrive at Russian Hill at 9:00 AM, travel to Pacific Heights takes 7 minutes
    arrival_time = 9 * 60        # 9:00 AM in minutes
    travel_time = 7              # 7 minutes
    earliest_start = arrival_time + travel_time  # 9:07 AM
    
    # Variables for the start and end of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')
    
    # Constraints
    s.add(meeting_start >= earliest_start)
    s.add(meeting_end == meeting_start + 60)  # Meeting lasts 60 minutes
    s.add(meeting_start >= barbara_start)
    s.add(meeting_end <= barbara_end)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start = m[meeting_start].as_long()
        end = m[meeting_end].as_long()
        # Convert back to human-readable time
        start_hour = start // 60
        start_min = start % 60
        end_hour = end // 60
        end_min = end % 60
        print(f"SOLUTION: Meet Barbara from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
    else:
        print("No valid meeting time found.")

solve_meeting_schedule()