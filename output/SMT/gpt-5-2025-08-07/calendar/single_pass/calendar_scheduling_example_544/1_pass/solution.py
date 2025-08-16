# Requires: z3-solver
# pip install z3-solver

from z3 import Solver, Int, Or, And, sat

def minutes(h, m=0):
    return h * 60 + m

def to_time_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Time bounds: Work hours 09:00 to 17:00 on Monday
    work_start = minutes(9, 0)   # 540
    work_end   = minutes(17, 0)  # 1020

    # Meeting duration: 30 minutes
    duration = 30

    # Participants' constraints on Monday
    # Deborah: free all day within work hours -> no extra blocks

    # Albert's blocked times (inclusive of start, exclusive of end)
    albert_blocks = [
        (minutes(9, 0),  minutes(10, 0)),   # 09:00-10:00
        (minutes(10, 30), minutes(12, 0)),  # 10:30-12:00
        (minutes(15, 0), minutes(16, 30)),  # 15:00-16:30
    ]

    # Albert cannot meet after 11:00 (meeting must fully finish by 11:00)
    albert_end_by = minutes(11, 0)

    # Z3 variables for meeting start and end in minutes since 00:00
    S = Int('start')  # start time
    E = Int('end')    # end time

    s = Solver()

    # Basic constraints: within work hours and fixed duration
    s.add(S >= work_start)
    s.add(E <= work_end)
    s.add(E == S + duration)

    # Albert cannot meet after 11:00
    s.add(E <= albert_end_by)

    # Non-overlap with Albert's blocked intervals
    for bstart, bend in albert_blocks:
        s.add(Or(E <= bstart, S >= bend))

    # Solve
    if s.check() != sat:
        print("No solution found")
        return

    model = s.model()
    start_val = model[S].as_long()
    end_val = model[E].as_long()

    # Output in required format
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")

if __name__ == "__main__":
    main()