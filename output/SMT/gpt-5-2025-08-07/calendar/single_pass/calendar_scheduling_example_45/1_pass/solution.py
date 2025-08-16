from z3 import Int, Optimize, Or, sat

def minutes(h, m):
    return h * 60 + m

def format_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Constants
    WORK_START = minutes(9, 0)
    WORK_END = minutes(17, 0)
    DURATION = 30  # minutes
    DAY = "Monday"

    # Participants' busy intervals as [start, end) in minutes from midnight
    # Andrew: none
    # Grace: none
    # Samuel: given busy slots
    samuel_busy = [
        (minutes(9, 0),  minutes(10, 30)),
        (minutes(11, 30), minutes(12, 0)),
        (minutes(13, 0),  minutes(13, 30)),
        (minutes(14, 0),  minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ]

    # Z3 variables
    start = Int('start')
    end = Int('end')

    opt = Optimize()
    opt.add(end == start + DURATION)
    opt.add(start >= WORK_START)
    opt.add(end <= WORK_END)

    # Meeting must not overlap with any of Samuel's busy intervals
    for (b_start, b_end) in samuel_busy:
        opt.add(Or(end <= b_start, start >= b_end))

    # Minimize the start time to get earliest availability
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found, despite the problem stating a solution exists.")

    model = opt.model()
    start_val = model[start].as_long()
    end_val = model[end].as_long()

    print("SOLUTION:")
    print(f"Day: {DAY}")
    print(f"Start Time: {format_time(start_val)}")
    print(f"End Time: {format_time(end_val)}")

if __name__ == "__main__":
    schedule_meeting()