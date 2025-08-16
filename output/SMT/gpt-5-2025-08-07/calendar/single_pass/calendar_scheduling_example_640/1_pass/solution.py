from z3 import Optimize, Int, Implies, Or, And

def parse_time_to_rel_minutes(t):
    # Convert "HH:MM" to minutes relative to 09:00 (workday start)
    h, m = map(int, t.split(":"))
    return h * 60 + m - 9 * 60

def minutes_to_hhmm(minutes_from_midnight):
    h = minutes_from_midnight // 60
    m = minutes_from_midnight % 60
    return f"{h:02d}:{m:02d}"

def main():
    days = ["Monday", "Tuesday"]
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # minutes
    day_window = work_end - work_start  # 480 minutes

    # Busy schedules
    busy = {
        "Monday": {
            "Bobby": [("14:30", "15:00")],
            "Michael": [("09:00", "10:00"), ("10:30", "13:30"), ("14:00", "15:00"), ("15:30", "17:00")],
        },
        "Tuesday": {
            "Bobby": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")],
            "Michael": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("15:00", "16:00"), ("16:30", "17:00")],
        },
    }

    # Build optimizer with lexicographic priority to get earliest day, then earliest time
    opt = Optimize()
    opt.set(priority='lex')

    day = Int('day')      # 0 = Monday, 1 = Tuesday
    start = Int('start')  # minutes from 09:00

    opt.add(day >= 0, day < len(days))
    opt.add(start >= 0, start + duration <= day_window)

    # No-overlap constraints for chosen day
    for d_idx, d_name in enumerate(days):
        for person, intervals in busy[d_name].items():
            for (s_str, e_str) in intervals:
                s = parse_time_to_rel_minutes(s_str)
                e = parse_time_to_rel_minutes(e_str)
                # Meeting [start, start+duration) must be outside [s, e)
                opt.add(Implies(day == d_idx, Or(start + duration <= s, start >= e)))

    # Earliest availability: minimize day first, then start time
    opt.minimize(day)
    opt.minimize(start)

    if opt.check() != 1:  # 1 == sat
        raise RuntimeError("No feasible solution found, but the problem states a solution exists.")

    m = opt.model()
    day_idx = m[day].as_long()
    start_rel = m[start].as_long()
    end_rel = start_rel + duration

    start_abs = work_start + start_rel
    end_abs = work_start + end_rel

    print("SOLUTION:")
    print(f"Day: {days[day_idx]}")
    print(f"Start Time: {minutes_to_hhmm(start_abs)}")
    print(f"End Time: {minutes_to_hhmm(end_abs)}")

if __name__ == "__main__":
    main()