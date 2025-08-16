from z3 import Int, Optimize, Or, And, sat

def minutes(h, m):
    return h * 60 + m

def format_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Work hours and duration
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30  # minutes

    # Slot-based modeling: 30-minute slots starting at 09:00 up to 16:30 inclusive
    max_slot = (work_end - work_start - duration) // 30  # 0..15
    start_slot = Int("start_slot")

    # Meeting start/end time expressions
    meeting_start = work_start + start_slot * 30
    meeting_end = meeting_start + duration

    opt = Optimize()
    opt.add(And(start_slot >= 0, start_slot <= max_slot))
    opt.add(And(meeting_start >= work_start, meeting_end <= work_end))

    # Helper to add non-overlap constraints against a list of busy intervals
    def add_no_overlap(busy_intervals):
        for (bs, be) in busy_intervals:
            opt.add(Or(meeting_end <= bs, meeting_start >= be))

    # Busy schedules (Monday)
    jose_busy = [
        (minutes(11, 0), minutes(11, 30)),
        (minutes(12, 30), minutes(13, 0)),
    ]
    keith_busy = [
        (minutes(14, 0), minutes(14, 30)),
        (minutes(15, 0), minutes(15, 30)),
    ]
    logan_busy = [
        (minutes(9, 0), minutes(10, 0)),
        (minutes(12, 0), minutes(12, 30)),
        (minutes(15, 0), minutes(15, 30)),
    ]
    megan_busy = [
        (minutes(9, 0), minutes(10, 30)),
        (minutes(11, 0), minutes(12, 0)),
        (minutes(13, 0), minutes(13, 30)),
        (minutes(14, 30), minutes(16, 30)),
    ]
    gary_busy = [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 0), minutes(10, 30)),
        (minutes(11, 30), minutes(13, 0)),
        (minutes(13, 30), minutes(14, 0)),
        (minutes(14, 30), minutes(16, 30)),
    ]
    bobby_busy = [
        (minutes(11, 0), minutes(11, 30)),
        (minutes(12, 0), minutes(12, 30)),
        (minutes(13, 0), minutes(16, 0)),
    ]

    # Add non-overlap constraints
    add_no_overlap(jose_busy)
    add_no_overlap(keith_busy)
    add_no_overlap(logan_busy)
    add_no_overlap(megan_busy)
    add_no_overlap(gary_busy)
    add_no_overlap(bobby_busy)

    # Jose preference: do not want to meet after 15:30 -> meeting must end by 15:30
    opt.add(meeting_end <= minutes(15, 30))

    # Find the earliest feasible start slot
    opt.minimize(start_slot)

    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found, but problem statement guarantees a solution.")

    model = opt.model()
    start_time = model.eval(meeting_start).as_long()
    end_time = model.eval(meeting_end).as_long()

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {format_time(start_time)} (24-hour format)")
    print(f"End Time: {format_time(end_time)} (24-hour format)")

if __name__ == "__main__":
    schedule_meeting()