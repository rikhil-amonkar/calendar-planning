from z3 import *

def schedule_meeting():
    solver = Solver()
    S = Int('S')
    solver.add(S >= 540)  # 9:00 AM in minutes
    solver.add(S <= 990)  # 4:30 PM in minutes (since meeting is 30 min)

    # All blocked intervals converted to minutes since midnight
    blocked_intervals = [
        # Doris
        (540, 660), (810, 840), (960, 990),
        # Theresa
        (600, 720),
        # Terry
        (570, 600), (690, 720), (750, 780), (810, 840), (870, 900), (930, 1020),
        # Carolyn
        (540, 630), (660, 690), (720, 780), (810, 870), (900, 1020),
        # Kyle
        (540, 570), (690, 720), (750, 780), (870, 1020)
    ]

    for b_start, b_end in blocked_intervals:
        solver.add(Or(S + 30 <= b_start, S >= b_end))

    if solver.check() == sat:
        model = solver.model()
        start_min = model[S].as_long()
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_min = start_min + 30
        end_hour = end_min // 60
        end_minute = end_min % 60

        def format_time(h, m):
            return f"{h:02d}:{m:02d}"

        day = "Monday"
        start_time = format_time(start_hour, start_minute)
        end_time = format_time(end_hour, end_minute)
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found.")

schedule_meeting()