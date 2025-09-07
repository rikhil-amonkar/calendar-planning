from z3 import *

def main():
    s = Int('s')
    opt = Optimize()

    # Work hours: 9:00 (540) to 17:00 (1020). Meeting is 30 min.
    # So start time must be between 540 and 990 (inclusive)
    opt.add(s >= 540)
    opt.add(s <= 990)

    # Cynthia's busy intervals
    busy_cynthia = [(570, 630), (690, 720), (780, 810), (900, 960)]
    for b_start, b_end in busy_cynthia:
        opt.add(Or(s + 30 <= b_start, s >= b_end))

    # Lauren's busy intervals
    busy_lauren = [(540, 570), (630, 660), (690, 720), (780, 810), (840, 870), (900, 930), (960, 1020)]
    for b_start, b_end in busy_lauren:
        opt.add(Or(s + 30 <= b_start, s >= b_end))

    # Robert's busy intervals
    busy_robert = [(630, 660), (690, 720), (750, 810), (840, 960)]
    for b_start, b_end in busy_robert:
        opt.add(Or(s + 30 <= b_start, s >= b_end))

    # Steven and Roy are free all day, no constraints

    # Minimize the start time
    opt.minimize(s)

    if opt.check() == sat:
        model = opt.model()
        start_time = model[s].as_long()
        end_time = start_time + 30
        # Convert to HH:MM format
        def to_time(mins):
            hours = mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"
        start_str = to_time(start_time)
        end_str = to_time(end_time)
        print(f"{start_str}:{end_str} Monday")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()