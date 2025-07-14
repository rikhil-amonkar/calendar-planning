from z3 import *

def solve_scheduling():
    # Define the work hours in minutes from 9:00 (0) to 17:00 (480)
    work_start = 0
    work_end = 480  # 8 hours * 60 minutes = 480 minutes (from 9:00 to 17:00)
    meeting_duration = 30  # minutes

    # Busy times for Lisa and Anthony in minutes from 9:00
    lisa_busy = [
        (0, 30),    # 9:00-9:30
        (90, 120),   # 10:30-11:00
        (300, 420)   # 14:00-16:00
    ]
    
    anthony_busy = [
        (0, 30),     # 9:00-9:30
        (120, 150),  # 11:00-11:30
        (210, 270),  # 12:30-13:30
        (300, 360),  # 14:00-15:00
        (390, 420),  # 15:30-16:00
        (450, 480)   # 16:30-17:00
    ]

    # Create a Z3 solver instance
    solver = Solver()

    # The meeting start time variable (in minutes from 9:00)
    meeting_start = Int('meeting_start')
    
    # Constraints:
    # 1. Meeting must start within work hours and end before work ends
    solver.add(meeting_start >= work_start)
    solver.add(meeting_start + meeting_duration <= work_end)
    
    # 2. Meeting must not overlap with Lisa's busy times
    for start, end in lisa_busy:
        solver.add(Or(
            meeting_start + meeting_duration <= start,
            meeting_start >= end
        ))
    
    # 3. Meeting must not overlap with Anthony's busy times
    for start, end in anthony_busy:
        solver.add(Or(
            meeting_start + meeting_duration <= start,
            meeting_start >= end
        ))
    
    # Find the earliest possible meeting time
    solver.push()
    earliest_time = None
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        earliest_time = model[meeting_start].as_long()
        # Verify it's the earliest by adding constraints to find times less than current solution
        while True:
            solver.push()
            solver.add(meeting_start < earliest_time)
            if solver.check() == sat:
                model = solver.model()
                earliest_time = model[meeting_start].as_long()
                solver.pop()
            else:
                solver.pop()
                break
    else:
        print("No solution found")
        return
    
    # Convert earliest_time back to HH:MM format
    start_hour = 9 + earliest_time // 60
    start_minute = earliest_time % 60
    end_time = earliest_time + meeting_duration
    end_hour = 9 + end_time // 60
    end_minute = end_time % 60
    
    # Format the output
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
    print(f"End Time: {end_hour:02d}:{end_minute:02d}")

solve_scheduling()