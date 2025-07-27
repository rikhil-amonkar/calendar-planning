from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days
    days = ['Monday', 'Tuesday', 'Wednesday']
    day = Int('day')
    s.add(day >= 0, day < len(days))  # 0: Monday, 1: Tuesday, 2: Wednesday

    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 60)  # 9:00 to 17:00 - 1 hour

    # Convert start time to HH:MM format
    def time_to_str(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"

    # Martha's blocked times (each is a list of (day, start, end) in minutes)
    martha_blocks = [
        (0, 960, 1020),   # Monday 16:00-17:00
        (1, 900, 930),     # Tuesday 15:00-15:30
        (2, 600, 660),     # Wednesday 10:00-11:00
        (2, 840, 870),     # Wednesday 14:00-14:30
    ]

    # Beverly's blocked times
    beverly_blocks = [
        (0, 540, 810),    # Monday 9:00-13:30
        (0, 840, 1020),    # Monday 14:00-17:00
        (1, 540, 1020),   # Tuesday 9:00-17:00
        (2, 570, 930),     # Wednesday 9:30-15:30
        (2, 990, 1020),    # Wednesday 16:30-17:00
    ]

    # Function to check if a time slot is blocked for a person
    def is_blocked(person_blocks, d, st, et):
        # Check each block for the person
        for block in person_blocks:
            block_day, block_st, block_et = block
            # If same day and overlapping times
            if d == block_day:
                if Not(Or(et <= block_st, st >= block_et)):
                    return True
        return False

    # The meeting duration is 1 hour (60 minutes)
    meeting_duration = 60
    end_time = start_time + meeting_duration

    # Add constraints that the meeting does not overlap with blocked times
    s.add(Not(is_blocked(martha_blocks, day, start_time, end_time)))
    s.add(Not(is_blocked(beverly_blocks, day, start_time, end_time)))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_idx = m[day].as_long()
        start = m[start_time].as_long()
        end = start + meeting_duration
        day_str = days[day_idx]
        start_str = time_to_str(start)
        end_str = time_to_str(end)
        print(f"SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()