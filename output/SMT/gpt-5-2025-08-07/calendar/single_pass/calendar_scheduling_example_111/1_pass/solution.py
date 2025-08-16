from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30  # minutes

    # Participants' blocked schedules (half-open intervals [start, end))
    schedules = {
        "Gregory": [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(11, 30)),
            (minutes(12, 30), minutes(13, 0)),
            (minutes(13, 30), minutes(14, 0)),
        ],
        "Natalie": [
            # Wide open: no blocks
        ],
        "Christine": [
            (minutes(9, 0), minutes(11, 30)),
            (minutes(13, 30), minutes(17, 0)),
        ],
        "Vincent": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 30), minutes(12, 0)),
            (minutes(12, 30), minutes(14, 0)),
            (minutes(14, 30), minutes(17, 0)),
        ],
    }

    s = Int('start_time')  # in minutes from 00:00
    e = s + duration

    solver = Solver()

    # Constrain meeting to be within work hours
    solver.add(s >= work_start)
    solver.add(e <= work_end)

    # For each participant and their blocked intervals, enforce non-overlap:
    # Meeting [s, e) does not overlap any blocked interval [b_s, b_e)
    for person, blocks in schedules.items():
        for b_s, b_e in blocks:
            solver.add(Or(e <= b_s, s >= b_e))

    if solver.check() != sat:
        raise RuntimeError("No feasible meeting time found, but one was expected.")

    model = solver.model()
    start_minutes = model[s].as_long()
    end_minutes = start_minutes + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_time(start_minutes)}")
    print(f"End Time: {fmt_time(end_minutes)}")

if __name__ == "__main__":
    main()