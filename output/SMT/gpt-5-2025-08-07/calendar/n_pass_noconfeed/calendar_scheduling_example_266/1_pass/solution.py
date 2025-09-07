# Scheduling a 30-minute meeting on Monday between 09:00 and 17:00 using Z3 SMT

from z3 import Int, Or, And, Optimize, sat

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def add_non_overlap(solver, start_var, duration, busy_intervals):
    for (b_start, b_end) in busy_intervals:
        # Meeting does not overlap a busy interval
        solver.add(Or(start_var + duration <= b_start, start_var >= b_end))

def main():
    day = "Monday"
    meeting_duration = 30  # minutes
    work_start = to_minutes(9, 0)
    work_end = to_minutes(17, 0)

    # Busy schedules (minutes from 00:00)
    Joe_busy = [
        (to_minutes(9,30), to_minutes(10,0)),
        (to_minutes(10,30), to_minutes(11,0)),
    ]

    Keith_busy = [
        (to_minutes(11,30), to_minutes(12,0)),
        (to_minutes(15,0), to_minutes(15,30)),
    ]

    Patricia_busy = [
        (to_minutes(9,0), to_minutes(9,30)),
        (to_minutes(13,0), to_minutes(13,30)),
    ]

    Nancy_busy = [
        (to_minutes(9,0), to_minutes(11,0)),
        (to_minutes(11,30), to_minutes(16,30)),
    ]

    Pamela_busy = [
        (to_minutes(9,0), to_minutes(10,0)),
        (to_minutes(10,30), to_minutes(11,0)),
        (to_minutes(11,30), to_minutes(12,30)),
        (to_minutes(13,0), to_minutes(14,0)),
        (to_minutes(14,30), to_minutes(15,0)),
        (to_minutes(15,30), to_minutes(16,0)),
        (to_minutes(16,30), to_minutes(17,0)),
    ]

    # Z3 model
    start = Int("start")
    opt = Optimize()

    # Working hours constraint
    opt.add(And(start >= work_start, start + meeting_duration <= work_end))

    # Non-overlap with each participant's busy times
    add_non_overlap(opt, start, meeting_duration, Joe_busy)
    add_non_overlap(opt, start, meeting_duration, Keith_busy)
    add_non_overlap(opt, start, meeting_duration, Patricia_busy)
    add_non_overlap(opt, start, meeting_duration, Nancy_busy)
    add_non_overlap(opt, start, meeting_duration, Pamela_busy)

    # Prefer earliest feasible time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        s = model[start].as_long()
        e = s + meeting_duration
        start_str = fmt_time(s)
        end_str = fmt_time(e)
        # Output must include both the time range (like {14:30:15:30}) and the day of the week
        print(day)
        print(f"{{{start_str}:{end_str}}}")
    else:
        print("No feasible meeting time found.")

if __name__ == "__main__":
    main()