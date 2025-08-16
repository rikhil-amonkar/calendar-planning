from z3 import *

def minutes_to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def main():
    # Variables
    day = Int("day")      # 0 = Monday, 1 = Tuesday
    start = Int("start")  # start time in minutes from 00:00
    duration = 60         # meeting duration in minutes

    opt = Optimize()

    # Work hours: 09:00 to 17:00
    opt.add(Or(day == 0, day == 1))
    opt.add(start >= 9 * 60)
    opt.add(start + duration <= 17 * 60)

    # Busy intervals in minutes (start, end), half-open [start, end)
    # Monday (0)
    monday_busy = [
        # Russell
        (10 * 60 + 30, 11 * 60 + 0),
        # Alexander
        (9 * 60, 11 * 60 + 30),
        (12 * 60, 14 * 60 + 30),
        (15 * 60, 17 * 60),
    ]

    # Tuesday (1)
    tuesday_busy = [
        # Russell
        (13 * 60, 13 * 60 + 30),
        # Alexander
        (9 * 60, 10 * 60),
        (13 * 60, 14 * 60),
        (15 * 60, 15 * 60 + 30),
        (16 * 60, 16 * 60 + 30),
    ]

    def no_overlap(d, bstart, bend):
        # Meeting [start, start+duration) does not overlap [bstart, bend)
        return If(day == d, Or(start + duration <= bstart, start >= bend), True)

    # Add non-overlap constraints conditioned on chosen day
    for b in monday_busy:
        opt.add(no_overlap(0, b[0], b[1]))
    for b in tuesday_busy:
        opt.add(no_overlap(1, b[0], b[1]))

    # Preference: Russell would rather not meet on Tuesday before 13:30 (soft constraint)
    opt.add_soft(Or(day != 1, start >= 13 * 60 + 30), weight="1", id="pref_after_1330_tue")

    if opt.check() != sat:
        raise RuntimeError("No solution found, but the problem statement guarantees one exists.")

    model = opt.model()
    dval = model[day].as_long()
    sval = model[start].as_long()
    eval_ = sval + duration

    day_name = "Monday" if dval == 0 else "Tuesday"

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {minutes_to_hhmm(sval)} (24-hour format)")
    print(f"End Time: {minutes_to_hhmm(eval_)} (24-hour format)")

if __name__ == "__main__":
    main()