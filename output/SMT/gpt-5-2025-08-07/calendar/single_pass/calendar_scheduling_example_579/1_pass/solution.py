from z3 import Optimize, Int, Or

def to_minutes(h, m):
    return h * 60 + m

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Meeting parameters
    duration = 30  # minutes
    day = "Monday"

    # Work hours
    work_start = to_minutes(9, 0)   # 09:00
    work_end   = to_minutes(17, 0)  # 17:00

    # Hard constraint: Helen cannot meet after 15:00 (meeting must finish by 15:00)
    helen_cutoff_end = to_minutes(15, 0)

    # Busy intervals for Monday (start, end) in minutes from 00:00
    christine_busy = [
        (to_minutes(11, 0), to_minutes(11, 30)),
        (to_minutes(15, 0), to_minutes(15, 30)),
    ]

    helen_busy = [
        (to_minutes(9, 30), to_minutes(10, 30)),
        (to_minutes(11, 0), to_minutes(11, 30)),
        (to_minutes(12, 0), to_minutes(12, 30)),
        (to_minutes(13, 30), to_minutes(16, 0)),
        (to_minutes(16, 30), to_minutes(17, 0)),
    ]

    # Z3 variables
    start = Int("start")
    end = Int("end")

    opt = Optimize()

    # Core constraints
    opt.add(end == start + duration)
    opt.add(start >= work_start)
    opt.add(end <= work_end)
    # Helen's constraint: no part of the meeting can be after 15:00
    opt.add(end <= helen_cutoff_end)

    # No overlap with Christine's busy times
    for s, e in christine_busy:
        opt.add(Or(end <= s, start >= e))

    # No overlap with Helen's busy times
    for s, e in helen_busy:
        opt.add(Or(end <= s, start >= e))

    # Optional: pick the earliest feasible start time
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found, but a solution was assumed to exist.")

    model = opt.model()
    start_min = model[start].as_long()
    end_min = model[end].as_long()

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_hhmm(start_min)}")
    print(f"End Time: {minutes_to_hhmm(end_min)}")

if __name__ == "__main__":
    main()