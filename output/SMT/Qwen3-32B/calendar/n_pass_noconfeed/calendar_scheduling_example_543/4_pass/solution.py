from z3 import *

def schedule_meeting():
    solver = Solver()
    start = Int('start')

    # Work hours from 9:00 (540) to 17:00 (1020)
    solver.add(And(start >= 540, start + 60 <= 1020))

    # James's availability constraints
    james_available = Or(
        And(start >= 540, start + 60 <= 690),  # 9:00-11:30
        And(start >= 720, start + 60 <= 870),  # 12:00-14:30
        And(start >= 900, start + 60 <= 1020)  # 15:00-17:00
    )
    solver.add(james_available)

    # John's availability constraints for one-hour meeting
    # Ensure the entire meeting is within John's available time
    john_available = And(start >= 780, start + 60 <= 870)  # 13:00-14:30
    solver.add(john_available)

    # Avoid the unavailable slot from 12:30 (750) to 13:30 (810)
    solver.add(Or(start + 60 <= 750, start >= 810))

    # Avoid the unavailable slot from 14:30 (870) to 15:00 (900)
    solver.add(Or(start < 870, start + 60 > 900))

    if solver.check() == sat:
        model = solver.model()
        start_val = model[start].as_long()
        day = "Monday"
        start_h = start_val // 60
        start_m = start_val % 60
        end_val = start_val + 60
        end_h = end_val // 60
        end_m = end_val % 60
        print(f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d} {day}")
    else:
        print("No solution")

schedule_meeting()