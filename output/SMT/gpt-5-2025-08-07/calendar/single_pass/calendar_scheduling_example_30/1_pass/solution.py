from z3 import Optimize, Int, Or

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # Work hours and meeting duration (in minutes)
    day = "Monday"
    work_start = 9 * 60      # 09:00
    work_end = 17 * 60       # 17:00
    duration = 30            # 30 minutes

    # Busy intervals as [start_minute, end_minute) in minutes since midnight
    jeffrey_busy = [
        (9*60 + 30, 10*60 + 0),   # 09:30 - 10:00
        (10*60 + 30, 11*60 + 0),  # 10:30 - 11:00
    ]
    virginia_busy = [
        (9*60 + 0, 9*60 + 30),    # 09:00 - 09:30
        (10*60 + 0, 10*60 + 30),  # 10:00 - 10:30
        (14*60 + 30, 15*60 + 0),  # 14:30 - 15:00
        (16*60 + 0, 16*60 + 30),  # 16:00 - 16:30
    ]
    melissa_busy = [
        (9*60 + 0, 11*60 + 30),   # 09:00 - 11:30
        (12*60 + 0, 12*60 + 30),  # 12:00 - 12:30
        (13*60 + 0, 15*60 + 0),   # 13:00 - 15:00
        (16*60 + 0, 17*60 + 0),   # 16:00 - 17:00
    ]

    # Preference: Melissa would rather not meet after 14:00 (treat as hard here)
    prefer_end_by = 14 * 60  # 14:00

    start = Int('start')
    end = Int('end')

    opt = Optimize()

    # Relationship and bounds
    opt.add(end == start + duration)
    opt.add(start >= work_start, end <= work_end)
    opt.add(end <= prefer_end_by)  # respect preference as a hard constraint

    # No-overlap constraints for each participant
    def no_overlap(busy_list):
        return [Or(end <= b_start, start >= b_end) for (b_start, b_end) in busy_list]

    for c in no_overlap(jeffrey_busy) + no_overlap(virginia_busy) + no_overlap(melissa_busy):
        opt.add(c)

    # Optional: choose the earliest feasible start
    opt.minimize(start)

    if opt.check() !=  sat:
        raise RuntimeError("No feasible schedule found, though the problem states one exists.")

    m = opt.model()
    s_val = m[start].as_long()
    e_val = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_hhmm(s_val)}")
    print(f"End Time: {minutes_to_hhmm(e_val)}")

if __name__ == "__main__":
    main()