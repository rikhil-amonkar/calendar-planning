from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the work hours (9:00 to 17:00) in minutes from 0 (9:00) to 480 (17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Define the possible start times (in minutes) for the meeting
    start_time = Int('start_time')
    s.add(start_time >= work_start)
    s.add(start_time <= work_end - meeting_duration)

    # Convert each participant's busy times to minutes from 0 (9:00)
    jeffrey_busy = [
        (9*60 + 30, 10*60),    # 9:30-10:00
        (10*60 + 30, 11*60)     # 10:30-11:00
    ]
    virginia_busy = [
        (9*60, 9*60 + 30),      # 9:00-9:30
        (10*60, 10*60 + 30),     # 10:00-10:30
        (14*60 + 30, 15*60),     # 14:30-15:00
        (16*60, 16*60 + 30)      # 16:00-16:30
    ]
    melissa_busy = [
        (9*60, 11*60 + 30),     # 9:00-11:30
        (12*60, 12*60 + 30),     # 12:00-12:30
        (13*60, 15*60),          # 13:00-15:00
        (16*60, 17*60)           # 16:00-17:00
    ]

    # Function to check if the meeting time overlaps with any busy time
    def no_overlap(start, busy_times):
        return And([Or(start + meeting_duration <= busy_start, start >= busy_end) 
                   for (busy_start, busy_end) in busy_times])

    # Add constraints for each participant
    s.add(no_overlap(start_time, jeffrey_busy))
    s.add(no_overlap(start_time, virginia_busy))
    s.add(no_overlap(start_time, melissa_busy))

    # Melissa's preference: meeting should not start after 14:00
    s.add(start_time <= 14 * 60)

    # Check for a solution
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

solve_scheduling_problem()