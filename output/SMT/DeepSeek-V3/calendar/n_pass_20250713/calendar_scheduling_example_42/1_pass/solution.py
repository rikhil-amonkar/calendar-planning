from z3 import *

def solve_scheduling():
    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Create a solver instance
    s = Solver()

    # Define the start time variable (in minutes from 0:00)
    start_time = Int('start_time')

    # Constraint: start time must be within work hours and the meeting must end before work ends
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Define the busy intervals for each participant in minutes
    julie_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (11 * 60, 11 * 60 + 30),   # 11:00-11:30
        (12 * 60, 12 * 60 + 30),   # 12:00-12:30
        (13 * 60 + 30, 14 * 60),   # 13:30-14:00
        (16 * 60, 17 * 60)         # 16:00-17:00
    ]
    sean_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (13 * 60, 13 * 60 + 30),   # 13:00-13:30
        (15 * 60, 15 * 60 + 30),   # 15:00-15:30
        (16 * 60, 16 * 60 + 30)    # 16:00-16:30
    ]
    lori_busy = [
        (10 * 60, 10 * 60 + 30),   # 10:00-10:30
        (11 * 60, 13 * 60),        # 11:00-13:00
        (15 * 60 + 30, 17 * 60)    # 15:30-17:00
    ]

    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(start, busy_intervals):
        return And([Or(start + meeting_duration <= busy_start, start >= busy_end) 
                    for (busy_start, busy_end) in busy_intervals])

    # Add constraints for each participant
    s.add(no_overlap(start_time, julie_busy))
    s.add(no_overlap(start_time, sean_busy))
    s.add(no_overlap(start_time, lori_busy))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start_time].as_long()
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