from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 = 9:00, 30 = 9:30)
    end_time = Int('end_time')

    # Constants
    meeting_duration = 30  # minutes
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 8 * 60  # 17:00 is 8 hours after 9:00 (480 minutes)

    # Constraints for day and time
    s.add(day >= 0, day <= 3)  # Monday (0) to Thursday (3)
    s.add(start_time >= work_start)
    s.add(end_time <= work_end)
    s.add(end_time == start_time + meeting_duration)

    # James's busy times per day in minutes from 9:00
    james_busy = {
        0: [(0, 30), (90, 120), (210, 240), (330, 390), (450, 480)],  # Monday
        1: [(0, 120), (150, 180), (210, 390), (420, 480)],             # Tuesday
        2: [(60, 120), (180, 240), (270, 420)],                        # Wednesday
        3: [(30, 150), (180, 210), (240, 270), (300, 330), (450, 480)] # Thursday
    }

    # Function to check if the meeting time overlaps with any busy slot
    def no_overlap(d, start, end):
        constraints = []
        if d in james_busy:
            for busy_start, busy_end in james_busy[d]:
                # No overlap if meeting is completely before or after the busy slot
                constraints.append(Or(end <= busy_start, start >= busy_end))
        return And(constraints) if constraints else True

    # Add constraints for no overlap with James's busy times
    for d in range(4):
        s.add(Implies(day == d, no_overlap(d, start_time, end_time)))

    # Cheryl's preferences: not Wednesday (2) or Thursday (3)
    # We'll first try to find a solution where day is Monday or Tuesday
    preferred_days = [0, 1]  # Monday and Tuesday
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(Or([day == d for d in preferred_days]))

    result = None
    if temp_solver.check() == sat:
        model = temp_solver.model()
        result = model
    else:
        # If no solution in preferred days, check all days
        if s.check() == sat:
            result = s.model()
        else:
            return None

    if result is None:
        return None

    # Extract solution
    day_val = result[day].as_long()
    start_val = result[start_time].as_long()
    end_val = result[end_time].as_long()

    # Convert day number to day name
    day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = day_names[day_val]

    # Convert start and end times to HH:MM format
    start_hh = 9 + start_val // 60
    start_mm = start_val % 60
    end_hh = 9 + end_val // 60
    end_mm = end_val % 60

    return {
        'day': day_name,
        'start_time': f"{start_hh:02d}:{start_mm:02d}",
        'end_time': f"{end_hh:02d}:{end_mm:02d}"
    }

solution = solve_scheduling()
if solution:
    print("SOLUTION:")
    print(f"Day: {solution['day']}")
    print(f"Start Time: {solution['start_time']}")
    print(f"End Time: {solution['end_time']}")
else:
    print("No solution found.")