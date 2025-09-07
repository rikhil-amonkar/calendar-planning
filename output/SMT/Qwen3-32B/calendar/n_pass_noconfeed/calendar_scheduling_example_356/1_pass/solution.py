from z3 import *

def main():
    s = Solver()

    start_time = Int('start_time')

    # Overall time constraints (9:00 to 17:00)
    s.add(start_time >= 540)  # 9:00 in minutes
    s.add(start_time + 30 <= 1020)  # 17:00 in minutes

    # Angela's preference: meeting after 15:00 (900 minutes)
    s.add(start_time >= 900)

    # Katherine's busy times
    for b_start, b_end in [(720, 750), (780, 870)]:
        s.add(Or(start_time + 30 <= b_start, start_time >= b_end))

    # Julie's busy times
    for b_start, b_end in [(540, 570), (630, 660), (810, 840), (900, 930)]:
        s.add(Or(start_time + 30 <= b_start, start_time >= b_end))

    # Angela's busy times
    for b_start, b_end in [(540, 600), (630, 660), (690, 840), (870, 900), (990, 1020)]:
        s.add(Or(start_time + 30 <= b_start, start_time >= b_end))

    # Nicholas's busy times
    for b_start, b_end in [(570, 660), (690, 810), (840, 960), (990, 1020)]:
        s.add(Or(start_time + 30 <= b_start, start_time >= b_end))

    # Carl's busy times
    for b_start, b_end in [(540, 660), (690, 750), (780, 870), (900, 960), (990, 1020)]:
        s.add(Or(start_time + 30 <= b_start, start_time >= b_end))

    if s.check() == sat:
        model = s.model()
        st = model[start_time].as_long()
        end_t = st + 30
        day = "Monday"
        # Convert minutes to HH:MM format
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        start_str = to_time(st)
        end_str = to_time(end_t)
        print(f"{start_str}:{end_str} {day}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()