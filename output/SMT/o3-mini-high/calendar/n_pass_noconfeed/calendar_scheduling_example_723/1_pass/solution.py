from z3 import Optimize, Int, Or, And, Implies, sat

# Meeting parameters
duration = 30  # duration in minutes
# Define meeting time as an offset (in minutes) from the start of the workday (9:00)
start = Int('start')
# Define day variable: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
day = Int('day')

opt = Optimize()

# Domain constraints for meeting start and day.
# Working hours are from 9:00 (offset 0) to 17:00 (offset 480),
# so the meeting must start no later than 450 (so that start + 30 <= 480).
opt.add(start >= 0, start <= 450)
# Allowed days are Monday, Tuesday, Wednesday but Arthur cannot meet on Tuesday.
opt.add(Or(day == 0, day == 2))

# ---------------------------
# Busy intervals (converted to minutes from 9:00)
# Monday:
# Arthur's meetings: [11:00-11:30] -> [120,150], [13:30-14:00] -> [270,300], [15:00-15:30] -> [360,390]
# Michael's meetings: [9:00-12:00] -> [0,180], [12:30-13:00] -> [210,240], [14:00-14:30] -> [300,330], [15:00-17:00] -> [360,480]
monday_constraints = []
# Arthur's constraints on Monday
monday_constraints.append(Or(start + duration <= 120, start >= 150))  # Avoid [120,150]
monday_constraints.append(Or(start + duration <= 270, start >= 300))  # Avoid [270,300]
monday_constraints.append(Or(start + duration <= 360, start >= 390))  # Avoid [360,390]
# Michael's constraints on Monday
monday_constraints.append(start >= 180)                              # Avoid [0,180]
monday_constraints.append(Or(start + duration <= 210, start >= 240))   # Avoid [210,240]
monday_constraints.append(Or(start + duration <= 300, start >= 330))   # Avoid [300,330]
monday_constraints.append(Or(start + duration <= 360, start >= 480))   # Avoid [360,480]

opt.add(Implies(day == 0, And(monday_constraints)))

# Wednesday:
# Arthur's meetings: [10:00-10:30] -> [60,90], [11:00-11:30] -> [120,150],
#                     [12:00-12:30] -> [180,210], [14:00-14:30] -> [300,330], [16:00-16:30] -> [420,450]
# Michael's meetings: [10:00-12:30] -> [60,210], [13:00-13:30] -> [240,270]
wednesday_constraints = []
# Arthur's constraints on Wednesday
wednesday_constraints.append(Or(start + duration <= 60, start >= 90))    # Avoid [60,90]
wednesday_constraints.append(Or(start + duration <= 120, start >= 150))  # Avoid [120,150]
wednesday_constraints.append(Or(start + duration <= 180, start >= 210))  # Avoid [180,210]
wednesday_constraints.append(Or(start + duration <= 300, start >= 330))  # Avoid [300,330]
wednesday_constraints.append(Or(start + duration <= 420, start >= 450))  # Avoid [420,450]
# Michael's constraints on Wednesday
wednesday_constraints.append(Or(start + duration <= 60, start >= 210))   # Avoid [60,210]
wednesday_constraints.append(Or(start + duration <= 240, start >= 270))  # Avoid [240,270]

opt.add(Implies(day == 2, And(wednesday_constraints)))

# ---------------------------
# We want the earliest availability: 
# first minimize the day (Monday=0 is preferred over Wednesday=2)
# then minimize the start time on that day.
h1 = opt.minimize(day)
h2 = opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    chosen_start_offset = m[start].as_long()  # minutes after 9:00
    # Convert offset into absolute minutes from midnight: 9:00 is 9*60 minutes.
    meeting_start_abs = 9 * 60 + chosen_start_offset
    meeting_end_abs = meeting_start_abs + duration

    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    # Map day to string.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_map[chosen_day]
    meeting_time_str = "{" + format_time(meeting_start_abs) + ":" + format_time(meeting_end_abs) + "}"
    
    print(day_str, meeting_time_str)
else:
    print("No solution found.")