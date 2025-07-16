from z3 import *

def find_meeting_time():
    # Initialize the solver
    s = Solver()

    # Define the start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    meeting_duration = 30  # minutes

    # Working hours: 9:00 (540) to 17:00 (1020)
    s.add(start_time >= 540)
    s.add(start_time + meeting_duration <= 1020)

    # Each participant's busy times in minutes from midnight
    # Format: list of (start, end) tuples for each participant
    andrea_busy = []
    jack_busy = [(540, 570), (840, 870)]
    madison_busy = [(570, 630), (780, 840), (900, 930), (990, 1020)]
    rachel_busy = [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)]
    douglas_busy = [(540, 690), (720, 990)]
    ryan_busy = [(540, 570), (780, 840), (870, 1020)]

    # Combine all busy times
    all_busy = jack_busy + madison_busy + rachel_busy + douglas_busy + ryan_busy

    # Add constraints that the meeting does not overlap with any busy time
    for (busy_start, busy_end) in all_busy:
        s.add(Or(
            start_time + meeting_duration <= busy_start,
            start_time >= busy_end
        ))

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert minutes back to HH:MM
        hours = start_min // 60
        minutes = start_min % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + meeting_duration
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

find_meeting_time()