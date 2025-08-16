from z3 import Optimize, Int, And, Or, If, Implies

def minutes(h, m):
    return h * 60 + m

def format_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Days mapping: 0=Monday, 1=Tuesday, 2=Wednesday
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}

    # Work hours
    WORK_START = minutes(9, 0)
    WORK_END = minutes(17, 0)
    MEETING_DURATION = 60

    # Busy schedules per person per day (times in minutes from 00:00 of that day)
    # Stephanie:
    stephanie_busy = {
        0: [  # Monday
            (minutes(9,30), minutes(10,0)),
            (minutes(10,30), minutes(11,0)),
            (minutes(11,30), minutes(12,0)),
            (minutes(14,0), minutes(14,30)),
        ],
        1: [  # Tuesday
            (minutes(12,0), minutes(13,0)),
        ],
        2: [  # Wednesday
            (minutes(9,0), minutes(10,0)),
            (minutes(13,0), minutes(14,0)),
        ],
    }

    # Betty:
    betty_busy = {
        0: [  # Monday
            (minutes(9,0), minutes(10,0)),
            (minutes(11,0), minutes(11,30)),
            (minutes(14,30), minutes(15,0)),
            (minutes(15,30), minutes(16,0)),
        ],
        1: [  # Tuesday
            (minutes(9,0), minutes(9,30)),
            (minutes(11,30), minutes(12,0)),
            (minutes(12,30), minutes(14,30)),
            (minutes(15,30), minutes(16,0)),
        ],
        2: [  # Wednesday
            (minutes(10,0), minutes(11,30)),
            (minutes(12,0), minutes(14,0)),
            (minutes(14,30), minutes(17,0)),
        ],
    }

    # Z3 variables
    day = Int("day")
    start = Int("start")
    end = Int("end")

    opt = Optimize()

    # Domain constraints
    opt.add(And(day >= 0, day <= 2))
    opt.add(And(start >= WORK_START, end == start + MEETING_DURATION, end <= WORK_END))

    # No overlap with busy times helper
    def add_no_overlap(person_busy):
        for d in [0, 1, 2]:
            for (b_start, b_end) in person_busy.get(d, []):
                # Meeting does not overlap: end <= busy_start OR start >= busy_end
                opt.add(Implies(day == d, Or(end <= b_start, start >= b_end)))

    add_no_overlap(stephanie_busy)
    add_no_overlap(betty_busy)

    # Preference/constraint:
    # - Stephanie would like to avoid Monday (soft preference)
    monday_penalty = If(day == 0, 1, 0)
    opt.minimize(monday_penalty)

    # - Betty cannot meet on Tuesday after 12:30 (hard constraint: meeting must end by 12:30 on Tuesday)
    opt.add(Implies(day == 1, end <= minutes(12, 30)))

    # Optional tie-breakers for determinism: prefer earlier day (Tue over Wed) and earlier start time
    opt.minimize(day)
    opt.minimize(start)

    if opt.check() != 1:  # 1 == sat
        raise RuntimeError("No feasible solution found, but one was expected.")

    model = opt.model()
    chosen_day = model.eval(day).as_long()
    start_min = model.eval(start).as_long()
    end_min = model.eval(end).as_long()

    print("SOLUTION:")
    print(f"Day: {day_names[chosen_day]}")
    print(f"Start Time: {format_time(start_min)}")
    print(f"End Time: {format_time(end_min)}")

if __name__ == "__main__":
    main()