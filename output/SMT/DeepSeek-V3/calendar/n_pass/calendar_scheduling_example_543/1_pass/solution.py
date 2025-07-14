from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define the busy slots for James and John in minutes since midnight
    james_busy = [
        (11 * 60 + 30, 12 * 60),    # 11:30-12:00
        (14 * 60 + 30, 15 * 60)     # 14:30-15:00
    ]
    john_busy = [
        (9 * 60 + 30, 11 * 60),     # 9:30-11:00
        (11 * 60 + 30, 12 * 60),    # 11:30-12:00
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30-13:30
        (14 * 60 + 30, 16 * 60 + 30)   # 14:30-16:30
    ]

    # Create a Z3 solver instance
    solver = Solver()

    # Define the start time of the meeting as a Z3 integer variable
    meeting_start = Int('meeting_start')
    
    # Constraint: meeting must start within work hours and end before work ends
    solver.add(meeting_start >= work_start)
    solver.add(meeting_start + meeting_duration <= work_end)

    # Constraint: meeting must not overlap with James's busy slots
    for start, end in james_busy:
        solver.add(Or(
            meeting_start + meeting_duration <= start,
            meeting_start >= end
        ))

    # Constraint: meeting must not overlap with John's busy slots
    for start, end in john_busy:
        solver.add(Or(
            meeting_start + meeting_duration <= start,
            meeting_start >= end
        ))

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_time = model[meeting_start].as_long()
        
        # Convert start time from minutes to HH:MM format
        start_hh = start_time // 60
        start_mm = start_time % 60
        start_str = f"{start_hh:02d}:{start_mm:02d}"
        
        # Calculate end time
        end_time = start_time + meeting_duration
        end_hh = end_time // 60
        end_mm = end_time % 60
        end_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found.")

find_meeting_time()