from z3 import *

def schedule_meeting():
    solver = Solver()
    S = Int('S')

    # Margaret's constraint: start time >= 14:30 (870 minutes) and meeting ends by 17:00 (1020)
    solver.add(S >= 870)
    solver.add(S <= 990)  # S + 30 <= 1020 => S <= 990

    # Define blocked intervals for each participant in minutes since midnight
    Shirley_intervals = [(630, 660), (720, 750)]
    Jacob_intervals = [(540, 570), (600, 630), (660, 690), (750, 810), (870, 900)]
    Stephen_intervals = [(690, 720), (750, 780)]
    Margaret_intervals = [(540, 570), (630, 750), (780, 810), (900, 930), (990, 1020)]
    Mason_intervals = [(540, 600), (630, 660), (690, 750), (780, 810), (840, 870), (990, 1020)]

    def add_constraints(intervals):
        for bs, be in intervals:
            solver.add(Or(S >= be, S + 30 <= bs))

    add_constraints(Shirley_intervals)
    add_constraints(Jacob_intervals)
    add_constraints(Stephen_intervals)
    add_constraints(Margaret_intervals)
    add_constraints(Mason_intervals)

    if solver.check() == sat:
        model = solver.model()
        start_min = model[S].as_long()
        end_min = start_min + 30

        def to_time(mins):
            hours = mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"

        day = "Monday"
        print(f"SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {to_time(start_min)}")
        print(f"End Time: {to_time(end_min)}")
    else:
        print("No solution found")

schedule_meeting()