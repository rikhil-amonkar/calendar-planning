from z3 import Solver, Int, Or

def to_minutes(h, m):
    return h * 60 + m

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Constants
    DAY = "Monday"
    WORK_START = to_minutes(9, 0)   # 09:00
    WORK_END = to_minutes(17, 0)    # 17:00
    DURATION = 30                   # 30 minutes
    HAROLD_END_LIMIT = to_minutes(13, 0)  # Harold does not want to meet after 13:00

    # Busy intervals as (start, end) in minutes since 00:00
    jacqueline_busy = [
        (to_minutes(9, 0), to_minutes(9, 30)),
        (to_minutes(11, 0), to_minutes(11, 30)),
        (to_minutes(12, 30), to_minutes(13, 0)),
        (to_minutes(15, 30), to_minutes(16, 0)),
    ]
    harold_busy = [
        (to_minutes(10, 0), to_minutes(10, 30)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(15, 0), to_minutes(17, 0)),
    ]
    arthur_busy = [
        (to_minutes(9, 0), to_minutes(9, 30)),
        (to_minutes(10, 0), to_minutes(12, 30)),
        (to_minutes(14, 30), to_minutes(15, 0)),
        (to_minutes(15, 30), to_minutes(17, 0)),
    ]
    kelly_busy = [
        (to_minutes(9, 0), to_minutes(9, 30)),
        (to_minutes(10, 0), to_minutes(11, 0)),
        (to_minutes(11, 30), to_minutes(12, 30)),
        (to_minutes(14, 0), to_minutes(15, 0)),
        (to_minutes(15, 30), to_minutes(16, 0)),
    ]

    # Z3 variables
    start = Int('start')
    end = Int('end')

    s = Solver()

    # Basic bounds within work hours
    s.add(start >= WORK_START)
    s.add(end <= WORK_END)
    s.add(end == start + DURATION)

    # Harold's preference: not after 13:00 => meeting must end by 13:00
    s.add(end <= HAROLD_END_LIMIT)

    # Non-overlapping constraints for each participant
    def add_non_overlap(busy_list):
        for (b_start, b_end) in busy_list:
            s.add(Or(end <= b_start, start >= b_end))

    add_non_overlap(jacqueline_busy)
    add_non_overlap(harold_busy)
    add_non_overlap(arthur_busy)
    add_non_overlap(kelly_busy)

    if s.check() != z3.sat:
        raise RuntimeError("No feasible meeting time found, though one was expected.")

    m = s.model()
    start_min = m[start].as_long()
    end_min = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {DAY}")
    print(f"Start Time: {format_time(start_min)} (24-hour format)")
    print(f"End Time: {format_time(end_min)} (24-hour format)")

if __name__ == "__main__":
    schedule_meeting()