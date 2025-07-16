from z3 import *

def solve_scheduling():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Define the blocked times for each participant in minutes since midnight
    kayla_blocked = [
        (10 * 60, 10 * 60 + 30),   # 10:00-10:30
        (14 * 60 + 30, 16 * 60)     # 14:30-16:00
    ]
    
    rebecca_blocked = [
        (9 * 60, 13 * 60),          # 9:00-13:00
        (13 * 60 + 30, 15 * 60),     # 13:30-15:00
        (15 * 60 + 30, 16 * 60)      # 15:30-16:00
    ]
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # The meeting duration is 1 hour (60 minutes)
    meeting_duration = 60
    
    # The start time of the meeting in minutes since midnight
    start_time = Int('start_time')
    
    # Constraints: start_time must be within work hours and the meeting must end within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)
    
    # Function to check if a time interval overlaps with any blocked intervals
    def no_overlap(start, duration, blocked_intervals):
        conditions = []
        for (block_start, block_end) in blocked_intervals:
            # The meeting interval does not overlap with the blocked interval
            conditions.append(Or(
                start + duration <= block_start,
                start >= block_end
            ))
        return And(conditions)
    
    # Add constraints for Kayla's blocked times
    solver.add(no_overlap(start_time, meeting_duration, kayla_blocked))
    
    # Add constraints for Rebecca's blocked times
    solver.add(no_overlap(start_time, meeting_duration, rebecca_blocked))
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.eval(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()