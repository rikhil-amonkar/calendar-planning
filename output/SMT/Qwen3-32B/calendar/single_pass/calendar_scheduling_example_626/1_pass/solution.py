from z3 import *

def main():
    solver = Solver()

    day = Int('day')
    start = Int('start')

    # Day must be 0 (Monday) or 1 (Tuesday)
    solver.add(Or(day == 0, day == 1))
    # Start time is between 9:00 (540) and 16:00 (960) inclusive
    solver.add(start >= 540)
    solver.add(start <= 960)

    # Patricia's Monday busy intervals
    p_mon = [(600, 630), (690, 720), (780, 810), (870, 930), (960, 990)]
    for b_s, b_e in p_mon:
        # If day is Monday (0), then start must not overlap with [b_s, b_e)
        solver.add(Or(day != 0, Or(start >= b_e, start + 60 <= b_s)))

    # Patricia's Tuesday busy intervals
    p_tue = [(600, 630), (660, 720), (840, 960), (990, 1020)]
    for b_s, b_e in p_tue:
        solver.add(Or(day != 1, Or(start >= b_e, start + 60 <= b_s)))

    # Jesse's Monday busy intervals
    j_mon = [(540, 1020)]
    for b_s, b_e in j_mon:
        solver.add(Or(day != 0, Or(start >= b_e, start + 60 <= b_s)))

    # Jesse's Tuesday busy intervals
    j_tue = [(660, 690), (720, 750), (780, 840), (870, 900), (930, 1020)]
    for b_s, b_e in j_tue:
        solver.add(Or(day != 1, Or(start >= b_e, start + 60 <= b_s)))

    if solver.check() == sat:
        m = solver.model()
        day_val = m[day].as_long()
        start_val = m[start].as_long()
        end_val = start_val + 60

        day_str = 'Monday' if day_val == 0 else 'Tuesday'

        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time_str = to_time_str(start_val)
        end_time_str = to_time_str(end_val)

        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()