from z3 import *

def minutes(h, m):
    return h * 60 + m

def format_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Constants
    WORK_START = minutes(9, 0)
    WORK_END = minutes(17, 0)
    DURATION = 60  # 1 hour
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

    # Busy schedules (minutes from 00:00)
    # Day index: 0=Mon, 1=Tue, 2=Wed, 3=Thu, 4=Fri
    diane_busy = {
        0: [(minutes(12, 0), minutes(12, 30)),
            (minutes(15, 0), minutes(15, 30))],
        1: [(minutes(10, 0), minutes(11, 0)),
            (minutes(11, 30), minutes(12, 0)),
            (minutes(12, 30), minutes(13, 0)),
            (minutes(16, 0), minutes(17, 0))],
        2: [(minutes(9, 0), minutes(9, 30)),
            (minutes(14, 30), minutes(15, 0)),
            (minutes(16, 30), minutes(17, 0))],
        3: [(minutes(15, 30), minutes(16, 30))],
        4: [(minutes(9, 30), minutes(11, 30)),
            (minutes(14, 30), minutes(15, 0)),
            (minutes(16, 0), minutes(17, 0))]
    }

    matthew_busy = {
        0: [(minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(17, 0))],
        1: [(minutes(9, 0), minutes(17, 0))],
        2: [(minutes(9, 0), minutes(11, 0)),
            (minutes(12, 0), minutes(14, 30)),
            (minutes(16, 0), minutes(17, 0))],
        3: [(minutes(9, 0), minutes(16, 0))],
        4: [(minutes(9, 0), minutes(17, 0))]
    }

    # Variables
    day = Int('day')         # 0..4 for Monday..Friday
    start = Int('start')     # minutes from 00:00 within the day

    s = Solver()

    # Domain constraints
    s.add(day >= 0, day <= 4)
    s.add(start >= WORK_START, start + DURATION <= WORK_END)

    # For each day, ensure no overlap with each person's busy intervals on that day
    def no_overlap_on_day(person_busy, d):
        intervals = person_busy.get(d, [])
        return And([Or(start + DURATION <= s0, start >= e0) for (s0, e0) in intervals])

    for d in range(5):
        s.add(Implies(day == d, no_overlap_on_day(diane_busy, d)))
        s.add(Implies(day == d, no_overlap_on_day(matthew_busy, d)))

    # Preference: Matthew would rather not meet on Wednesday before 12:30
    # Treating as a strict constraint
    s.add(Implies(day == 2, start >= minutes(12, 30)))

    if s.check() != sat:
        print("No solution found.")
        return

    m = s.model()
    d_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + DURATION

    day_name = days[d_val]
    start_str = format_time(start_val)
    end_str = format_time(end_val)

    # Output must include both the day and the time range in {HH:MM:HH:MM}
    print(f"{day_name} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()