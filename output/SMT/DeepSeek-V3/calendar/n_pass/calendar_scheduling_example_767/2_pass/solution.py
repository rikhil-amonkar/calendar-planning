from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days
    days = ['Monday', 'Tuesday', 'Wednesday']
    day = Int('day')
    s.add(day >= 0, day < len(days))  # 0: Monday, 1: Tuesday, 2: Wednesday

    # Define the start time in minutes from 0:00 (easier for calculations)
    start_time = Int('start_time')
    # Meeting must be between 9:00 (540) and 17:00 (1020), duration 60 minutes
    s.add(start_time >= 540, start_time <= 1020 - 60)

    # Convert minutes to HH:MM format
    def time_to_str(t):
        h = t // 60
        m = t % 60
        return f"{h:02d}:{m:02d}"

    # Martha's blocked times (day, start_min, end_min)
    martha_blocks = [
        (0, 960, 1020),   # Monday 16:00-17:00
        (1, 900, 930),     # Tuesday 15:00-15:30
        (2, 600, 660),     # Wednesday 10:00-11:00
        (2, 840, 870),     # Wednesday 14:00-14:30
    ]

    # Beverly's blocked times
    beverly_blocks = [
        (0, 540, 810),    # Monday 9:00-13:30
        (0, 840, 1020),   # Monday 14:00-17:00
        (1, 540, 1020),   # Tuesday 9:00-17:00 (entire day)
        (2, 570, 930),    # Wednesday 9:30-15:30
        (2, 990, 1020),   # Wednesday 16:30-17:00
    ]

    # Function to check if time range [st, et) is available on given day
    def is_available(day_idx, st, et, blocks):
        for block in blocks:
            block_day, block_st, block_et = block
            if day_idx == block_day:
                # If there's any overlap between [st, et) and [block_st, block_et)
                if Not(Or(et <= block_st, st >= block_et)):
                    return False
        return True

    meeting_duration = 60
    end_time = start_time + meeting_duration

    # Constraints for Martha's availability
    martha_available = Bool('martha_available')
    s.add(martha_available == is_available(day, start_time, end_time, martha_blocks))
    s.add(martha_available)

    # Constraints for Beverly's availability
    beverly_available = Bool('beverly_available')
    s.add(beverly_available == is_available(day, start_time, end_time, beverly_blocks))
    s.add(beverly_available)

    # Check for solution
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