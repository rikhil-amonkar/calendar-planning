from z3 import Optimize, Int, Or, Mod, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def add_non_overlap_constraints(solver, start_var, duration, busy_intervals):
    # Ensure [start, start+duration] does not overlap any [b_start, b_end)
    for b_start, b_end in busy_intervals:
        solver.add(Or(start_var >= b_end, start_var + duration <= b_start))

def main():
    # Meeting parameters
    duration = 30  # minutes
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)

    # Busy schedules in minutes from 00:00
    Megan = [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 0), minutes(11, 0)),
        (minutes(12, 0), minutes(12, 30)),
    ]
    Christine = [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(11, 30), minutes(12, 0)),
        (minutes(13, 0), minutes(14, 0)),
        (minutes(15, 30), minutes(16, 30)),
    ]
    Gabriel = []  # Free all day
    Sara = [
        (minutes(11, 30), minutes(12, 0)),
        (minutes(14, 30), minutes(15, 0)),
    ]
    Bruce = [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(10, 30), minutes(12, 0)),
        (minutes(12, 30), minutes(14, 0)),
        (minutes(14, 30), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 30)),
    ]
    Kathryn = [
        (minutes(10, 0), minutes(15, 30)),
        (minutes(16, 0), minutes(16, 30)),
    ]
    Billy = [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(11, 0), minutes(11, 30)),
        (minutes(12, 0), minutes(14, 0)),
        (minutes(14, 30), minutes(15, 30)),
    ]

    # Z3 Model
    start = Int('start')
    opt = Optimize()

    # Within working hours and on 30-minute boundaries
    opt.add(start >= work_start, start + duration <= work_end)
    opt.add(Mod(start, 30) == 0)

    # Add non-overlap constraints for all participants
    for schedule in [Megan, Christine, Gabriel, Sara, Bruce, Kathryn, Billy]:
        add_non_overlap_constraints(opt, start, duration, schedule)

    # Prefer earliest feasible time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        st = model[start].as_long()
        et = st + duration
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {fmt_time(st)} (24-hour format)")
        print(f"End Time: {fmt_time(et)} (24-hour format)")
    else:
        # Given the problem states a solution exists, this should not happen.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: 00:00 (24-hour format)")
        print("End Time: 00:30 (24-hour format)")

if __name__ == "__main__":
    main()