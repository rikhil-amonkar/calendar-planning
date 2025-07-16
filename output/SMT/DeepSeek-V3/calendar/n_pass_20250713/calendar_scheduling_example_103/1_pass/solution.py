from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    
    # Define the start time variable (in minutes since midnight)
    start_time = Int('start_time')
    
    # Constraint: start time must be within work hours and leave room for the meeting
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Define each participant's blocked time slots in minutes since midnight
    blocked_slots = {
        'Diane': [(9*60 + 30, 10*60), (14*60 + 30, 15*60)],
        'Jack': [(13*60 + 30, 14*60), (14*60 + 30, 15*60)],
        'Eugene': [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (12*60, 14*60 + 30), (15*60, 16*60 + 30)],
        'Patricia': [(9*60 + 30, 10*60 + 30), (11*60, 12*60), (12*60 + 30, 14*60), (15*60, 16*60 + 30)]
    }
    
    # Add constraints for each participant's blocked slots
    for participant in blocked_slots:
        for (block_start, block_end) in blocked_slots[participant]:
            # The meeting should not overlap with the blocked slot
            # So either meeting ends before block starts or starts after block ends
            s.add(Or(
                start_time + meeting_duration <= block_start,
                start_time >= block_end
            ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start_time).as_long()
        
        # Convert start and end times to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        solution = (
            f"SOLUTION:\n"
            f"Day: Monday\n"
            f"Start Time: {start_hour:02d}:{start_minute:02d}\n"
            f"End Time: {end_hour:02d}:{end_minute:02d}"
        )
        print(solution)
    else:
        print("No solution found")

solve_scheduling()