from z3 import Int, Optimize, Or, Implies, sat

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create an optimizer instance
opt = Optimize()

# Variables:
# meeting_day: 1 = Monday, 2 = Tuesday, 3 = Wednesday
# meeting_start: meeting start time in minutes from midnight.
meeting_day = Int('meeting_day')
meeting_start = Int('meeting_start')
meeting_duration = 60
meeting_end = meeting_start + meeting_duration

# Working hours: meeting must be between 9:00 (540 minutes) and 17:00 (1020 minutes).
opt.add(meeting_start >= 540, meeting_end <= 1020)
opt.add(Or(meeting_day == 1, meeting_day == 2, meeting_day == 3))

# Roy's busy intervals for each day (times in minutes from midnight):
# Monday: [10:00-11:30], [12:00-13:00], [14:00-14:30], [15:00-17:00]
monday_busy = [(600, 690), (720, 780), (840, 870), (900, 1020)]
# Tuesday: [10:30-11:30], [12:00-14:30], [15:00-15:30], [16:00-17:00]
tuesday_busy = [(630, 690), (720, 870), (900, 930), (960, 1020)]
# Wednesday: [9:30-11:30], [12:30-14:00], [14:30-15:30], [16:30-17:00]
wednesday_busy = [(570, 690), (750, 840), (870, 930), (990, 1020)]

# Add constraints for Roy's availability on Monday
for bstart, bend in monday_busy:
    # For a busy interval, the meeting must end before it starts, or start after it ends.
    opt.add(Implies(meeting_day == 1, Or(meeting_end <= bstart, meeting_start >= bend)))
    
# Tuesday constraints
for bstart, bend in tuesday_busy:
    opt.add(Implies(meeting_day == 2, Or(meeting_end <= bstart, meeting_start >= bend)))
    
# Wednesday constraints
for bstart, bend in wednesday_busy:
    opt.add(Implies(meeting_day == 3, Or(meeting_end <= bstart, meeting_start >= bend)))

# The meeting should be scheduled at the earliest availability.
# We achieve a lexicographic minimization: earliest day (1 < 2 < 3) and then earliest start time.
# We encode it as a single objective: meeting_day * 10000 + meeting_start.
objective = meeting_day * 10000 + meeting_start
opt.minimize(objective)

if opt.check() == sat:
    model = opt.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    day_map = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}
    day_name = day_map.get(day_val, "Unknown")
    time_range = f"{minutes_to_time(start_val)}:{minutes_to_time(end_val)}"

    print(f"{day_name} {time_range}")
else:
    print("No valid meeting time found.")