# Requires: z3-solver
# Task: Schedule a 30-minute meeting for Judy and Nicole on Monday between 09:00 and 17:00.
# Judy is free all day. Nicole is busy 09:00-10:00 and 10:30-16:30.
# Preference: Nicole would rather not meet before 16:00.

from z3 import Int, Or, Optimize

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Constants
    DAY = "Monday"
    WORK_START = 9 * 60      # 09:00
    WORK_END = 17 * 60       # 17:00
    DURATION = 30            # 30 minutes

    # Participants' busy schedules (half-open intervals [start, end))
    # Judy: free all day within work hours
    busy_nicole = [
        (9 * 60, 10 * 60),            # 09:00 - 10:00
        (10 * 60 + 30, 16 * 60 + 30)  # 10:30 - 16:30
    ]

    # SMT variables
    s = Int("start")  # start time in minutes since 00:00
    e = s + DURATION

    opt = Optimize()

    # Working hours constraint
    opt.add(s >= WORK_START, e <= WORK_END)

    # Nicole's busy-time constraints (no overlap with meeting)
    for bs, be in busy_nicole:
        opt.add(Or(e <= bs, s >= be))

    # Preference: Nicole would rather not meet before 16:00
    opt.add_soft(s >= 16 * 60, weight="1", id="prefer_after_16")

    if opt.check().r == 1:  # sat
        model = opt.model()
        start_m = model[s].as_long()
        end_m = start_m + DURATION
        start_str = minutes_to_hhmm(start_m)
        end_str = minutes_to_hhmm(end_m)

        # Output: day of the week and time range in {HH:MM:HH:MM}
        print(DAY)
        print(f"{{{start_str}:{end_str}}}")
    else:
        print("No feasible meeting time found.")

if __name__ == "__main__":
    main()