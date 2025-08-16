from z3 import Solver, Int, Or, And, sat

def t(h, m):  # convert hour, minute to minutes since 00:00
    return h * 60 + m

def format_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    work_start = t(9, 0)
    work_end = t(17, 0)
    duration = 30

    # Busy intervals per participant (start, end) in minutes since midnight
    busy = {
        "Emily": [(t(10, 0), t(10, 30)), (t(16, 0), t(16, 30))],
        "Mason": [],
        "Maria": [(t(10, 30), t(11, 0)), (t(14, 0), t(14, 30))],
        "Carl": [(t(9, 30), t(10, 0)), (t(10, 30), t(12, 30)), (t(13, 30), t(14, 0)),
                 (t(14, 30), t(15, 30)), (t(16, 0), t(17, 0))],
        "David": [(t(9, 30), t(11, 0)), (t(11, 30), t(12, 0)), (t(12, 30), t(13, 30)),
                  (t(14, 0), t(15, 0)), (t(16, 0), t(17, 0))],
        "Frank": [(t(9, 30), t(10, 30)), (t(11, 0), t(11, 30)), (t(12, 30), t(13, 30)),
                  (t(14, 30), t(17, 0))],
    }

    # Z3 variable for meeting start time (in minutes since midnight)
    S = Int("S")

    # Build a solver with general constraints once
    solver = Solver()
    # Meeting must be within work hours
    solver.add(S >= work_start)
    solver.add(S + duration <= work_end)
    # Start times aligned to 30-minute grid
    solver.add(S % 30 == 0)

    # No overlap with any busy interval for each participant
    for person, intervals in busy.items():
        for (bs, be) in intervals:
            # Meeting [S, S+duration) does not overlap with [bs, be)
            solver.add(Or(S + duration <= bs, S >= be))

    # Search for the earliest feasible 30-minute slot
    found_start = None
    for candidate in range(work_start, work_end - duration + 1, 30):
        solver.push()
        solver.add(S == candidate)
        if solver.check() == sat:
            found_start = candidate
            solver.pop()
            break
        solver.pop()

    if found_start is None:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")

    start_time = format_hhmm(found_start)
    end_time = format_hhmm(found_start + duration)

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time} (24-hour format)")
    print(f"End Time: {end_time} (24-hour format)")

if __name__ == "__main__":
    main()