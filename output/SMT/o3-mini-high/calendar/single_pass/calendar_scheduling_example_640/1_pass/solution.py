from z3 import Optimize, Int, Or, Implies

# Represent time in minutes since midnight for convenience.
# Work day is from 09:00 (540 min) to 17:00 (1020 min).
WORK_START = 540
WORK_END = 1020
MEETING_DURATION = 30

# We use an integer for the meeting start time (in minutes) and an integer for the day.
# We'll encode Monday as 0 and Tuesday as 1.
day = Int("day")  # 0: Monday, 1: Tuesday
s = Int("s")      # meeting start time in minutes

# List of busy intervals (start, end) for each participant on each day.
# Times are in minutes since midnight.
# Bobby's busy intervals:
bobby_busy_mon = [(870, 900)]  # 14:30 to 15:00 on Monday
bobby_busy_tue = [(540, 690),  # 9:00 to 11:30 on Tuesday
                  (720, 750),  # 12:00 to 12:30 on Tuesday
                  (780, 900),  # 13:00 to 15:00 on Tuesday
                  (930, 1020)] # 15:30 to 17:00 on Tuesday

# Michael's busy intervals:
michael_busy_mon = [(540, 600),  # 9:00 to 10:00 on Monday
                    (630, 810),  # 10:30 to 13:30 on Monday
                    (840, 900),  # 14:00 to 15:00 on Monday
                    (930, 1020)] # 15:30 to 17:00 on Monday
michael_busy_tue = [(540, 630),  # 9:00 to 10:30 on Tuesday
                    (660, 690),  # 11:00 to 11:30 on Tuesday
                    (720, 840),  # 12:00 to 14:00 on Tuesday
                    (900, 960),  # 15:00 to 16:00 on Tuesday
                    (990, 1020)] # 16:30 to 17:00 on Tuesday

# Create our optimizer (we use Optimize because we need the earliest availability).
opt = Optimize()

# Constraints for the day: day must be either 0 (Monday) or 1 (Tuesday)
opt.add(Or(day == 0, day == 1))

# Constraint for the meeting start time within working hours.
opt.add(s >= WORK_START)
opt.add(s + MEETING_DURATION <= WORK_END)

# Helper: for a given busy interval, the meeting [s, s+MEETING_DURATION] must not overlap it.
def non_overlap_constraint(busy_interval):
    busy_start, busy_end = busy_interval
    # Either the meeting must end before the busy period starts,
    # or it must start after the busy period ends.
    return Or(s + MEETING_DURATION <= busy_start, s >= busy_end)

# Add constraints for Bobby on Monday (day==0) and Tuesday (day==1).
for interval in bobby_busy_mon:
    opt.add(Implies(day == 0, non_overlap_constraint(interval)))
for interval in bobby_busy_tue:
    opt.add(Implies(day == 1, non_overlap_constraint(interval)))

# Add constraints for Michael on Monday (day==0) and Tuesday (day==1).
for interval in michael_busy_mon:
    opt.add(Implies(day == 0, non_overlap_constraint(interval)))
for interval in michael_busy_tue:
    opt.add(Implies(day == 1, non_overlap_constraint(interval)))

# We want to choose the earliest time (first Monday if possible, then earliest time on that day).
# We can combine the day and the time by minimizing day*1440 + s (since there are 1440 minutes in a day).
opt.minimize(day * 1440 + s)

if opt.check() == sat:
    m = opt.model()
    day_val = m.evaluate(day).as_long()
    s_val = m.evaluate(s).as_long()
    meeting_day = "Monday" if day_val == 0 else "Tuesday"
    start_minutes = s_val
    end_minutes = s_val + MEETING_DURATION

    # Function to convert minutes since midnight to HH:MM (24-hour format)
    def minutes_to_hhmm(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"

    print("SOLUTION:")
    print("Day:", meeting_day)
    print("Start Time:", minutes_to_hhmm(start_minutes))
    print("End Time:", minutes_to_hhmm(end_minutes))
else:
    print("No solution found.")