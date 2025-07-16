from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Meeting duration is 1 hour (60 minutes)
    meeting_duration = 60

    # Define the start time of the meeting in minutes since midnight
    start_time = Int('start_time')

    # Constraint: Meeting must start within work hours and end by work end time
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Define the busy slots for each participant in minutes since midnight
    ryan_busy = [(9 * 60, 9 * 60 + 30), (12 * 60 + 30, 13 * 60)]
    denise_busy = [(9 * 60 + 30, 10 * 60 + 30), (12 * 60, 13 * 60), (14 * 60 + 30, 16 * 60 + 30)]
    ruth_busy = []  # Ruth has no meetings

    # Constraint: Meeting should not overlap with Ryan's busy slots
    for (busy_start, busy_end) in ryan_busy:
        s.add(Or(
            start_time + meeting_duration <= busy_start,
            start_time >= busy_end
        ))

    # Constraint: Meeting should not overlap with Denise's busy slots
    for (busy_start, busy_end) in denise_busy:
        s.add(Or(
            start_time + meeting_duration <= busy_start,
            start_time >= busy_end
        ))

    # Constraint: Denise does not want to meet after 12:30 (12:30 is 12*60 + 30 = 750 minutes)
    s.add(start_time + meeting_duration <= 12 * 60 + 30)

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + meeting_duration
        end_hour = end_min // 60
        end_minute = end_min % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()