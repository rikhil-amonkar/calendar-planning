from z3 import Optimize, Int, Or

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Constants
    WORK_START = 9 * 60
    WORK_END = 17 * 60
    DURATION = 30

    # Create optimizer
    opt = Optimize()

    # Variables: start and end times in minutes from 00:00
    start = Int('start')
    end = Int('end')

    # Hard constraints: within work hours and fixed duration
    opt.add(start >= WORK_START)
    opt.add(end == start + DURATION)
    opt.add(end <= WORK_END)

    # Participant schedules (busy intervals are [start, end) in minutes)
    # Judy: free all day -> no constraints

    # Nicole's busy times on Monday
    nicole_busy = [
        (9 * 60, 10 * 60),
        (10 * 60 + 30, 16 * 60 + 30),
    ]

    # No overlap with Nicole's busy intervals
    for b_start, b_end in nicole_busy:
        opt.add(Or(end <= b_start, start >= b_end))

    # Preference: Nicole would rather not meet before 16:00 (soft constraint)
    opt.add_soft(start >= 16 * 60, weight=1)

    # Optionally, choose the latest feasible time (helps pick the end of day if multiple)
    opt.maximize(start)

    if opt.check() != 1:  # sat
        raise RuntimeError("No feasible schedule found, but the problem statement guarantees one.")

    model = opt.model()
    s = model.eval(start).as_long()
    e = model.eval(end).as_long()

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {minutes_to_hhmm(s)}")
    print(f"End Time: {minutes_to_hhmm(e)}")

if __name__ == "__main__":
    main()