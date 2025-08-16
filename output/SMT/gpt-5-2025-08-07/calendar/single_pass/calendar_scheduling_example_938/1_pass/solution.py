# Requires: z3-solver
# You can install with: pip install z3-solver

from z3 import Optimize, Int, If, Or, And, Mod

# Time helpers
def to_min(h, m):
    return h * 60 + m

def fmt_time(mn):
    h = mn // 60
    m = mn % 60
    return f"{h:02d}:{m:02d}"

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
MON, TUE, WED, THU, FRI = range(5)

# Work hours and meeting duration
WORK_START = to_min(9, 0)
WORK_END   = to_min(17, 0)
MEET_DUR   = 30

# Busy schedules as [start, end) in minutes from 00:00
EUGENE_BUSY = {
    MON: [(to_min(11,0), to_min(12,0)),
          (to_min(13,30), to_min(14,0)),
          (to_min(14,30), to_min(15,0)),
          (to_min(16,0), to_min(16,30))],
    WED: [(to_min(9,0), to_min(9,30)),
          (to_min(11,0), to_min(11,30)),
          (to_min(12,0), to_min(12,30)),
          (to_min(13,30), to_min(15,0))],
    THU: [(to_min(9,30), to_min(10,0)),
          (to_min(11,0), to_min(12,30))],
    FRI: [(to_min(10,30), to_min(11,0)),
          (to_min(12,0), to_min(12,30)),
          (to_min(13,0), to_min(13,30))],
}

ERIC_BUSY = {
    MON: [(to_min(9,0), to_min(17,0))],
    TUE: [(to_min(9,0), to_min(17,0))],
    WED: [(to_min(9,0), to_min(11,30)),
          (to_min(12,0), to_min(14,0)),
          (to_min(14,30), to_min(16,30))],
    THU: [(to_min(9,0), to_min(17,0))],
    FRI: [(to_min(9,0), to_min(11,0)),
          (to_min(11,30), to_min(17,0))],
}

def add_non_overlap(opt, day_var, start_var, end_var, busy_dict):
    # Meeting [start,end) must not overlap any busy [s,e) on that day
    for d in range(5):
        for (s, e) in busy_dict.get(d, []):
            opt.add(Or(day_var != d, end_var <= s, start_var >= e))

def solve_meeting():
    opt = Optimize()
    opt.set(priority='lex')  # honor objectives in the order added

    day = Int('day')          # 0..4 (Mon..Fri)
    start = Int('start')      # minutes from 00:00
    end = Int('end')          # minutes from 00:00

    # Domain constraints
    opt.add(day >= 0, day <= 4)
    opt.add(end == start + MEET_DUR)
    opt.add(start >= WORK_START)
    opt.add(end <= WORK_END)

    # Align to 30-minute increments (optional but typical)
    opt.add(Mod(start - WORK_START, 30) == 0)

    # Non-overlap with each participant's busy times
    add_non_overlap(opt, day, start, end, EUGENE_BUSY)
    add_non_overlap(opt, day, start, end, ERIC_BUSY)

    # Preference: Eric would like to avoid more meetings on Wednesday
    avoid_wed_penalty = If(day == WED, 1, 0)
    opt.minimize(avoid_wed_penalty)

    # Tie-breakers: earliest day (after respecting preference), then earliest start time
    opt.minimize(day)
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting found (unexpected for this task).")

    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    chosen_end = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {days[chosen_day]}")
    print(f"Start Time: {fmt_time(chosen_start)} (24-hour format)")
    print(f"End Time: {fmt_time(chosen_end)} (24-hour format)")

if __name__ == "__main__":
    solve_meeting()