from z3 import Int, Or, And, Optimize, sat

def minutes_since(day_start_h, day_start_m, h, m):
    return (h - day_start_h) * 60 + (m - day_start_m)

def format_time(day_start_h, total_minutes):
    h = day_start_h + total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    work_start_h, work_start_m = 9, 0
    work_end_h, work_end_m = 17, 0
    meeting_duration = 30  # minutes

    # Convert work hours to minutes from day start
    work_start = minutes_since(work_start_h, work_start_m, work_start_h, work_start_m)  # 0
    work_end = minutes_since(work_start_h, work_start_m, work_end_h, work_end_m)        # 480

    # Busy schedules (start and end are in absolute HH:MM of the same day)
    # Adam's busy times
    adam_busy_abs = [
        (9, 30, 10, 0),
        (12, 30, 13, 0),
        (14, 30, 15, 0),
        (16, 30, 17, 0),
    ]
    # Roy's busy times
    roy_busy_abs = [
        (10, 0, 11, 0),
        (11, 30, 13, 0),
        (13, 30, 14, 30),
        (16, 30, 17, 0),
    ]

    # Convert busy times to minutes since work_start
    def to_minutes_intervals(busy_abs):
        intervals = []
        for sh, sm, eh, em in busy_abs:
            s = minutes_since(work_start_h, work_start_m, sh, sm)
            e = minutes_since(work_start_h, work_start_m, eh, em)
            intervals.append((s, e))  # [s, e)
        return intervals

    adam_busy = to_minutes_intervals(adam_busy_abs)
    roy_busy = to_minutes_intervals(roy_busy_abs)

    # Z3 model
    o = Optimize()
    s = Int("start")  # meeting start time in minutes since work_start

    # Domain constraints
    o.add(s >= work_start)
    o.add(s + meeting_duration <= work_end)

    # Non-overlap constraints for each participant
    def no_overlap_with(intervals):
        # For meeting [s, s+dur), ensure it does not intersect any [b_start, b_end)
        return [Or(s + meeting_duration <= b_start, s >= b_end) for (b_start, b_end) in intervals]

    o.add(And(*no_overlap_with(adam_busy)))
    o.add(And(*no_overlap_with(roy_busy)))

    # Earliest availability: minimize start time
    o.minimize(s)

    if o.check() != sat:
        print("No feasible meeting time found.")
        return

    m = o.model()
    start_min = m[s].as_long()
    end_min = start_min + meeting_duration

    start_str = format_time(work_start_h, start_min)
    end_str = format_time(work_start_h, end_min)

    # Output day and time range in required format
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()