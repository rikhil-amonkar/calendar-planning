from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    start_time = Int('start_time')  # in minutes from 00:00
    end_time = Int('end_time')

    # Constraints for day (0-4 representing Monday to Friday)
    s.add(day >= 0, day <= 4)

    # Meeting must be within work hours (9:00 to 17:00)
    s.add(start_time >= 9 * 60, end_time <= 17 * 60)
    s.add(end_time == start_time + 60)

    # Define busy slots for Nicole and Daniel
    # Each entry is (day, start, end) in minutes from 00:00
    nicole_busy = [
        (1, 16*60, 16*60 + 30),  # Tuesday 16:00-16:30
        (2, 15*60, 15*60 + 30),   # Wednesday 15:00-15:30
        (4, 12*60, 12*60 + 30),   # Friday 12:00-12:30
        (4, 15*60 + 30, 16*60)    # Friday 15:30-16:00
    ]

    daniel_busy = [
        (0, 9*60, 12*60 + 30),    # Monday 9:00-12:30
        (0, 13*60, 13*60 + 30),   # Monday 13:00-13:30
        (0, 14*60, 16*60 + 30),   # Monday 14:00-16:30
        (1, 9*60, 10*60 + 30),    # Tuesday 9:00-10:30
        (1, 11*60 + 30, 12*60 + 30),  # Tuesday 11:30-12:30
        (1, 13*60, 13*60 + 30),    # Tuesday 13:00-13:30
        (1, 15*60, 16*60),        # Tuesday 15:00-16:00
        (1, 16*60 + 30, 17*60),   # Tuesday 16:30-17:00
        (2, 9*60, 10*60),         # Wednesday 9:00-10:00
        (2, 11*60, 12*60 + 30),   # Wednesday 11:00-12:30
        (2, 13*60, 13*60 + 30),    # Wednesday 13:00-13:30
        (2, 14*60, 14*60 + 30),    # Wednesday 14:00-14:30
        (2, 16*60 + 30, 17*60),   # Wednesday 16:30-17:00
        (3, 11*60, 12*60),        # Thursday 11:00-12:00
        (3, 13*60, 14*60),        # Thursday 13:00-14:00
        (3, 15*60, 15*60 + 30),   # Thursday 15:00-15:30
        (4, 10*60, 11*60),        # Friday 10:00-11:00
        (4, 11*60 + 30, 12*60),   # Friday 11:30-12:00
        (4, 12*60 + 30, 14*60 + 30),  # Friday 12:30-14:30
        (4, 15*60, 15*60 + 30),   # Friday 15:00-15:30
        (4, 16*60, 16*60 + 30)    # Friday 16:00-16:30
    ]

    # Function to check no overlap with busy slots
    def no_overlap(d, start, end, busy_slots):
        return And([Or(d != slot[0], end <= slot[1], start >= slot[2]) for slot in busy_slots])

    # Add constraints for Nicole and Daniel
    s.add(no_overlap(day, start_time, end_time, nicole_busy))
    s.add(no_overlap(day, start_time, end_time, daniel_busy))

    # To find the earliest time, we minimize (day * 1440 + start_time)
    # Create an optimization solver
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(day * 1440 + start_time)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        d = m[day].as_long()
        start = m[start_time].as_long()
        end = m[end_time].as_long()

        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        selected_day = days[d]
        start_hh = start // 60
        start_mm = start % 60
        end_hh = end // 60
        end_mm = end % 60

        # Formatting to ensure two digits for minutes
        start_str = f"{start_hh:02d}:{start_mm:02d}"
        end_str = f"{end_hh:02d}:{end_mm:02d}"

        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()