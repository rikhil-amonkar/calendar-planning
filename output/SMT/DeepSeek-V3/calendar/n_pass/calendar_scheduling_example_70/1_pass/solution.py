from z3 import *

def find_meeting_time():
    # Participants' busy slots in minutes since 9:00 (540 minutes)
    # Work hours: 9:00 (540) to 17:00 (1020)
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Convert each participant's busy times to minutes since 9:00
    denise_busy = [(720, 750), (930, 960)]  # 12:00-12:30, 15:30-16:00
    angela_busy = []  # No meetings
    natalie_busy = [(540, 690), (720, 780), (840, 870), (900, 1020)]  # 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00

    # Create a solver instance
    solver = Solver()

    # The meeting start time (in minutes since 9:00)
    start = Int('start')
    end = start + meeting_duration

    # Constraints: start must be within work hours and end must be <= work_end
    solver.add(start >= work_start)
    solver.add(end <= work_end)

    # Add constraints for each participant's busy times
    # Denise's constraints: meeting must not overlap with any of her busy slots
    for (busy_start, busy_end) in denise_busy:
        solver.add(Or(end <= busy_start, start >= busy_end))
    
    # Angela has no constraints, so no additions needed
    
    # Natalie's constraints
    for (busy_start, busy_end) in natalie_busy:
        solver.add(Or(end <= busy_start, start >= busy_end))
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_time_min = model[start].as_long()
        
        # Convert start_time_min back to HH:MM format
        hours = start_time_min // 60
        minutes = start_time_min % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_time_min = start_time_min + meeting_duration
        end_hours = end_time_min // 60
        end_minutes = end_time_min % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

find_meeting_time()