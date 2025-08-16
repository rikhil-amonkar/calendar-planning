from z3 import *

def main():
    solver = Optimize()
    start = Int('start')

    # Work hours: 9:00 AM to 5:00 PM => 540 to 1020 minutes
    # Meeting duration is 30 minutes => start must be <= 990
    solver.add(start >= 540)
    solver.add(start <= 990)

    # Eric's blocked intervals (in minutes since midnight)
    eric_blocked = [(720, 780), (840, 900)]  # 12:00-13:00, 14:00-15:00

    # Henry's blocked intervals
    henry_blocked = [
        (570, 600),   # 9:30-10:00
        (630, 660),   # 10:30-11:00
        (690, 750),   # 11:30-12:30
        (780, 810),   # 13:00-13:30
        (870, 900),   # 14:30-15:00
        (960, 1020)   # 16:00-17:00
    ]

    # Add constraints to avoid overlapping with blocked intervals
    for s, e in eric_blocked + henry_blocked:
        solver.add(Or(start >= e, start + 30 <= s))

    # Minimize the start time to respect Henry's preference
    solver.minimize(start)

    if solver.check() == sat:
        model = solver.model()
        start_val = model[start].as_long()
        end_val = start_val + 30

        def to_time(mins):
            hours = mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"

        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {to_time(start_val)}")
        print(f"End Time: {to_time(end_val)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()