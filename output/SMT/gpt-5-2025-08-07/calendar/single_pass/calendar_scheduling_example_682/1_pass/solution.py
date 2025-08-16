from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Days mapping
    MON, TUE = 0, 1
    day_names = {MON: "Monday", TUE: "Tuesday"}

    # Work hours: 09:00 to 17:00
    WORK_START = minutes(9, 0)
    WORK_END = minutes(17, 0)

    # Meeting duration: 30 minutes
    DURATION = 30

    # Busy schedules in minutes [start, end)
    # Amanda
    amanda_busy = {
        MON: [
            (minutes(9, 0),  minutes(10, 30)),
            (minutes(11, 0), minutes(11, 30)),
            (minutes(12, 30), minutes(13, 0)),
            (minutes(13, 30), minutes(14, 0)),
            (minutes(14, 30), minutes(15, 0)),
        ],
        TUE: [
            (minutes(9, 0),  minutes(9, 30)),
            (minutes(10, 0), minutes(10, 30)),
            (minutes(11, 30), minutes(12, 0)),
            (minutes(13, 30), minutes(14, 30)),
            (minutes(15, 30), minutes(16, 0)),
            (minutes(16, 30), minutes(17, 0)),
        ]
    }

    # Nathan
    nathan_busy = {
        MON: [
            (minutes(10, 0), minutes(10, 30)),
            (minutes(11, 0), minutes(11, 30)),
            (minutes(13, 30), minutes(14, 30)),
            (minutes(16, 0), minutes(16, 30)),
        ],
        TUE: [
            (minutes(9, 0),  minutes(10, 30)),
            (minutes(11, 0), minutes(13, 0)),
            (minutes(13, 30), minutes(14, 0)),
            (minutes(14, 30), minutes(15, 30)),
            (minutes(16, 0), minutes(16, 30)),
        ]
    }

    # Z3 variables
    day = Int("day")          # 0 = Monday, 1 = Tuesday
    start = Int("start")      # minutes from 00:00
    end = Int("end")

    s = Solver()

    # Day domain
    s.add(Or(day == MON, day == TUE))

    # Meeting duration and work hours within the selected day
    s.add(end == start + DURATION)
    s.add(start >= WORK_START, end <= WORK_END)

    # Helper to assert no overlap with a set of busy intervals for a given person
    def no_overlap_for_person(person_busy):
        constraints = []
        for d in [MON, TUE]:
            for (b_start, b_end) in person_busy[d]:
                # No overlap: [start, end) does not intersect [b_start, b_end)
                constraints.append(If(day == d, Or(end <= b_start, b_end <= start), True))
        return And(constraints)

    s.add(no_overlap_for_person(amanda_busy))
    s.add(no_overlap_for_person(nathan_busy))

    # Additional constraints:
    # Amanda does not want to meet on Tuesday after 11:00 -> if Tuesday, meeting must end by 11:00.
    s.add(If(day == TUE, end <= minutes(11, 0), True))

    # Nathan cannot meet on Monday -> force Tuesday
    s.add(day == TUE)

    # Optionally, find the earliest feasible time (minimize start)
    # Using Optimize to be deterministic and pick earliest slot
    opt = Optimize()
    for c in s.assertions():
        opt.add(c)
    h = opt.minimize(start)
    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found.")
    m = opt.model()

    sel_day = m[day].as_long()
    sel_start = m[start].as_long()
    sel_end = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {day_names[sel_day]}")
    print(f"Start Time: {minutes_to_str(sel_start)} (24-hour format)")
    print(f"End Time: {minutes_to_str(sel_end)} (24-hour format)")

if __name__ == "__main__":
    schedule_meeting()