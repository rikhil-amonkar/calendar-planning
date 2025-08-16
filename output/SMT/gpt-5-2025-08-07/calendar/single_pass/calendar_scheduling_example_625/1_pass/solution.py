from z3 import Int, Optimize, And, Or, Implies, Mod

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def no_overlap_constraint(start, dur, intervals):
    # For each busy interval [s, e), enforce meeting [start, start+dur) is outside it.
    return And([Or(start + dur <= s, start >= e) for (s, e) in intervals]) if intervals else True

def solve():
    # Constants
    MONDAY, TUESDAY = 0, 1
    WORK_START = minutes(9, 0)
    WORK_END   = minutes(17, 0)
    DURATION   = 30

    # Schedules (Jeffrey is free all week; only Harold has blocks)
    harold_busy = {
        MONDAY:  [(minutes(9,0), minutes(10,0)), (minutes(10,30), minutes(17,0))],
        TUESDAY: [(minutes(9,0), minutes(9,30)), (minutes(10,30), minutes(11,30)),
                  (minutes(12,30), minutes(13,30)), (minutes(14,30), minutes(15,30)),
                  (minutes(16,0), minutes(17,0))]
    }

    # Z3 variables
    day = Int('day')    # 0=Monday, 1=Tuesday
    start = Int('start')  # minutes from 00:00 on the chosen day

    opt = Optimize()

    # Domain constraints
    opt.add(Or(day == MONDAY, day == TUESDAY))
    opt.add(start >= WORK_START)
    opt.add(start + DURATION <= WORK_END)
    opt.add(Mod(start, 30) == 0)  # 30-minute increments

    # Availability constraints for Harold (Jeffrey is free)
    opt.add(Implies(day == MONDAY, no_overlap_constraint(start, DURATION, harold_busy[MONDAY])))
    opt.add(Implies(day == TUESDAY, no_overlap_constraint(start, DURATION, harold_busy[TUESDAY])))

    # Preferences (soft constraints)
    # Prefer Tuesday over Monday (weight 2)
    opt.add_soft(day == TUESDAY, weight='2')
    # If Tuesday, prefer start at or after 14:30 (weight 1)
    opt.add_soft(Implies(day == TUESDAY, start >= minutes(14,30)), weight='1')

    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found, but problem statement guarantees a solution.")

    m = opt.model()
    chosen_day = m[day].as_long()
    start_time = m[start].as_long()
    end_time = start_time + DURATION

    day_str = "Monday" if chosen_day == MONDAY else "Tuesday"

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {minutes_to_str(start_time)}")
    print(f"End Time: {minutes_to_str(end_time)}")

if __name__ == "__main__":
    solve()