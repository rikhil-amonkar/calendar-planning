from z3 import Int, Optimize, sat, Or, Implies

# Create an Optimize instance
opt = Optimize()

# Decision variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
day = Int("day")
# start is the meeting start time in minutes after 9:00.
start = Int("start")
duration = 30
end = start + duration

# Domain constraints
opt.add(day >= 0, day <= 2)
# Arthur cannot meet on Tuesday.
opt.add(day != 1)
# Meeting must fall within work hours (9:00 to 17:00, i.e. 480 minutes from 9:00).
opt.add(start >= 0, end <= 480)

# Busy intervals are represented as tuples: (day, busy_start, busy_end)
# times are in minutes offset from 9:00.
busy_intervals = []

# Arthur's busy intervals:
# Monday (day = 0)
busy_intervals.append((0, 120, 150))  # 11:00-11:30 (11:00 = 120 minutes after 9:00)
busy_intervals.append((0, 270, 300))  # 13:30-14:00
busy_intervals.append((0, 360, 390))  # 15:00-15:30
# Tuesday (day = 1) -- even though Arthur is unavailable on Tuesday, we add these for completeness.
busy_intervals.append((1, 240, 270))  # 13:00-13:30
busy_intervals.append((1, 420, 450))  # 16:00-16:30
# Wednesday (day = 2)
busy_intervals.append((2, 60, 90))    # 10:00-10:30
busy_intervals.append((2, 120, 150))  # 11:00-11:30
busy_intervals.append((2, 180, 210))  # 12:00-12:30
busy_intervals.append((2, 300, 330))  # 14:00-14:30
busy_intervals.append((2, 420, 450))  # 16:00-16:30

# Michael's busy intervals:
# Monday (day = 0)
busy_intervals.append((0, 0, 180))    # 9:00-12:00
busy_intervals.append((0, 210, 240))  # 12:30-13:00
busy_intervals.append((0, 300, 330))  # 14:00-14:30
busy_intervals.append((0, 360, 480))  # 15:00-17:00
# Tuesday (day = 1)
busy_intervals.append((1, 30, 150))   # 9:30-11:30 (since 9:30 = 30 minutes after 9:00)
busy_intervals.append((1, 180, 270))  # 12:00-13:30
busy_intervals.append((1, 300, 390))  # 14:00-15:30
# Wednesday (day = 2)
busy_intervals.append((2, 60, 210))   # 10:00-12:30
busy_intervals.append((2, 240, 270))  # 13:00-13:30

# For each busy interval, if the meeting is on the same day, it must not overlap the busy time.
for b_day, b_start, b_end in busy_intervals:
    opt.add(Implies(day == b_day, Or(end <= b_start, start >= b_end)))

# Objective: meet at the earliest availability.
# We'll minimize a combined objective: day*10000 + start. This makes Monday (day 0) always be preferred to Wednesday (day 2),
# and within a day, an earlier start time is preferred.
objective = day * 10000 + start
opt.minimize(objective)

# Solve the constraints.
if opt.check() == sat:
    m = opt.model()
    meeting_day = m[day].as_long()
    meeting_start = m[start].as_long()
    meeting_end = meeting_start + duration

    # Convert meeting_start (minutes after 9:00) to HH:MM format.
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60

    # Map day integer to day name.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    
    # Print the solution in the required format.
    print("SOLUTION:")
    print(f"Day: {day_map[meeting_day]}")
    print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
    print(f"End Time: {end_hour:02d}:{end_minute:02d}")
else:
    print("No solution found.")