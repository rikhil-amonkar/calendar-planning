from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 00:00
    end_time = Int('end_time')

    # Define the constraints for day and time
    s.add(day >= 0, day <= 3)  # Monday to Thursday
    # Working hours 9:00 to 17:00 (540 to 1020 minutes)
    s.add(start_time >= 540, end_time <= 1020)
    s.add(end_time == start_time + 30)  # 30 minutes duration

    # Mary's busy times (each entry is (day, start, end) in minutes from 00:00)
    mary_busy = [
        (1, 600, 630),   # Tuesday 10:00-10:30
        (1, 930, 960),    # Tuesday 15:30-16:00
        (2, 570, 600),    # Wednesday 9:30-10:00
        (2, 900, 930),    # Wednesday 15:00-15:30
        (3, 540, 600),    # Thursday 9:00-10:00
        (3, 630, 690)     # Thursday 10:30-11:30
    ]

    # Alexis's busy times
    alexis_busy = [
        (0, 540, 600),    # Monday 9:00-10:00
        (0, 630, 720),    # Monday 10:30-12:00
        (0, 750, 990),    # Monday 12:30-16:30
        (1, 540, 600),    # Tuesday 9:00-10:00
        (1, 630, 690),    # Tuesday 10:30-11:30
        (1, 720, 930),    # Tuesday 12:00-15:30
        (1, 960, 1020),   # Tuesday 16:00-17:00
        (2, 540, 660),     # Wednesday 9:00-11:00
        (2, 690, 1020),    # Wednesday 11:30-17:00
        (3, 600, 720),     # Thursday 10:00-12:00
        (3, 840, 870),     # Thursday 14:00-14:30
        (3, 930, 960),     # Thursday 15:30-16:00
        (3, 990, 1020)     # Thursday 16:30-17:00
    ]

    # Function to check if two intervals overlap
    def overlaps(a_start, a_end, b_start, b_end):
        return Or(
            And(a_start >= b_start, a_start < b_end),
            And(a_end > b_start, a_end <= b_end),
            And(a_start <= b_start, a_end >= b_end)
        )

    # Add constraints that the meeting does not overlap with Mary's busy times
    for m_day, m_start, m_end in mary_busy:
        s.add(Not(And(day == m_day, overlaps(start_time, end_time, m_start, m_end))))

    # Add constraints for Alexis's busy times
    for a_day, a_start, a_end in alexis_busy:
        s.add(Not(And(day == a_day, overlaps(start_time, end_time, a_start, a_end))))

    # To find the earliest time, we minimize (day * 1440 + start_time)
    # 1440 is the number of minutes in a day
    opt = Optimize()
    opt.add(s.assertions())
    cost = day * 1440 + start_time
    opt.minimize(cost)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        d = model[day].as_long()
        st = model[start_time].as_long()
        et = model[end_time].as_long()

        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[d]

        # Convert start and end times to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = minutes_to_time(st)
        end_str = minutes_to_time(et)

        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()