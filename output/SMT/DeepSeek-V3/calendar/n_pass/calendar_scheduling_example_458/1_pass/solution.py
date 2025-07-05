from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the possible meeting start times (in minutes from 9:00)
    start_time = Int('start_time')
    meeting_duration = 30  # minutes

    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    min_time = 9 * 60  # 9:00 in minutes
    max_time = 17 * 60 - meeting_duration  # Latest start time is 16:30

    # Constraint: start_time must be within work hours
    s.add(start_time >= min_time, start_time <= max_time)

    # Wayne's preference: avoid meetings before 14:00
    s.add(start_time >= 14 * 60)

    # Define each participant's busy times in minutes from 9:00
    # Format: list of (start, end) intervals
    busy_times = {
        'Melissa': [(10*60, 11*60), (12*60 + 30, 14*60), (15*60, 15*60 + 30)],
        'Gregory': [(12*60 + 30, 13*60), (15*60 + 30, 16*60)],
        'Victoria': [(9*60, 9*60 + 30), (10*60 + 30, 11*60 + 30), (13*60, 14*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60 + 30)],
        'Thomas': [(10*60, 12*60), (12*60 + 30, 13*60), (14*60 + 30, 16*60)],
        'Jennifer': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60, 13*60), (13*60 + 30, 14*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)],
    }

    # For each participant, add constraints that the meeting does not overlap with their busy times
    for person in busy_times:
        for (busy_start, busy_end) in busy_times[person]:
            # The meeting does not overlap with this busy interval
            s.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_time].as_long()
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60

        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()