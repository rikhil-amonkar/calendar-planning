from z3 import *

def solve_scheduling():
    # Initialize the optimizer
    opt = Optimize()

    # Work hours: 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60

    # Meeting duration: 30 minutes
    duration = 30

    # Define the start time of the meeting in minutes since midnight
    start_time = Int('start_time')
    end_time = start_time + duration

    # Constraint: meeting must be within work hours
    opt.add(start_time >= work_start)
    opt.add(end_time <= work_end)

    # Participants' busy times in minutes since midnight
    # Andrew and Grace are free all day, so no constraints
    # Samuel's busy times: 9:00-10:30, 11:30-12:00, 13:00-13:30, 14:00-16:00, 16:30-17:00
    samuel_busy = [
        (9 * 60, 10 * 60 + 30),
        (11 * 60 + 30, 12 * 60),
        (13 * 60, 13 * 60 + 30),
        (14 * 60, 16 * 60),
        (16 * 60 + 30, 17 * 60)
    ]

    # Constraint: meeting must not overlap with Samuel's busy times
    for busy_start, busy_end in samuel_busy:
        opt.add(Or(
            end_time <= busy_start,
            start_time >= busy_end
        ))

    # Find the earliest possible meeting time by minimizing start_time
    opt.minimize(start_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        earliest_start = m[start_time].as_long()
        earliest_end = earliest_start + duration

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        start_str = minutes_to_time(earliest_start)
        end_str = minutes_to_time(earliest_end)

        return f"""SOLUTION:
Day: Monday
Start Time: {start_str}
End Time: {end_str}"""
    else:
        return "No solution found"

print(solve_scheduling())