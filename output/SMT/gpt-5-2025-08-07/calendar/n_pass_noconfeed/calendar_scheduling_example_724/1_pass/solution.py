from z3 import *

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def build_solver(include_preference=True):
    # Variables
    day = Int('day')          # 0=Monday, 1=Tuesday, 2=Wednesday
    start = Int('start')      # minutes from 00:00
    end = Int('end')

    s = Solver()

    # Constants
    MON, TUE, WED = 0, 1, 2
    WORK_START = 9 * 60
    WORK_END = 17 * 60
    DURATION = 30

    # Day domain
    s.add(And(day >= MON, day <= WED))

    # Meeting duration and within work hours
    s.add(end == start + DURATION)
    s.add(start >= WORK_START, end <= WORK_END)

    # Align to 30-minute boundaries
    s.add(start % 30 == 0)

    # Busy schedules (in minutes since midnight)
    # Tyler
    tyler_busy = {
        MON: [],
        TUE: [(9*60, 9*60+30), (14*60+30, 15*60)],
        WED: [(10*60+30, 11*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)]
    }
    # Ruth
    ruth_busy = {
        MON: [(9*60,10*60),(10*60+30,12*60),(12*60+30,14*60+30),(15*60,16*60),(16*60+30,17*60)],
        TUE: [(9*60,17*60)],
        WED: [(9*60,17*60)]
    }

    # No overlap constraints
    for (d, intervals) in tyler_busy.items():
        for (bs, be) in intervals:
            s.add(Implies(day == d, Or(end <= bs, start >= be)))
    for (d, intervals) in ruth_busy.items():
        for (bs, be) in intervals:
            s.add(Implies(day == d, Or(end <= bs, start >= be)))

    # Preference: Tyler would like to avoid Monday before 16:00
    # Encode as a soft-like preference by first trying with it enforced, and fallback later if needed.
    if include_preference:
        s.add(Or(day != MON, start >= 16*60))

    return s, day, start, end

def solve_with_preference_then_relax():
    # First, try satisfying the preference
    s1, day1, start1, end1 = build_solver(include_preference=True)
    if s1.check() == sat:
        m = s1.model()
        return m[day1].as_long(), m[start1].as_long(), m[end1].as_long()

    # If not satisfiable, relax the preference
    s2, day2, start2, end2 = build_solver(include_preference=False)
    assert s2.check() == sat
    m = s2.model()
    return m[day2].as_long(), m[start2].as_long(), m[end2].as_long()

if __name__ == "__main__":
    day_val, start_val, end_val = solve_with_preference_then_relax()
    day_names = ["Monday", "Tuesday", "Wednesday"]
    start_str = minutes_to_str(start_val)
    end_str = minutes_to_str(end_val)
    print(f"{day_names[day_val]} {{{start_str}:{end_str}}}")