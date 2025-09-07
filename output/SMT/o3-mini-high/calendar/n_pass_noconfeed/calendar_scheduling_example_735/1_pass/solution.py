from z3 import Optimize, Int, Or, Implies, sat

# meeting duration in minutes
meeting_duration = 30

# Create an Optimize instance (for optimization objectives)
opt = Optimize()

# Define variables:
# 'day' is an integer representing the day: 0 for Monday, 1 for Tuesday, 2 for Wednesday.
# 'start' is the meeting start time in minutes offset from 9:00.
day = Int('day')
start = Int('start')

# Working hours: meeting must start between 9:00 and 16:30 (i.e. start in [0, 450]).
opt.add(Or(day == 0, day == 1, day == 2))
opt.add(start >= 0, start <= 450)

# Busy intervals are given relative to 9:00. For instance, 9:30 -> 30, 10:30 -> 90, etc.

# Monday busy intervals (in minutes):
# Ronald: 10:30-11:00 -> (90,120), 12:00-12:30 -> (180,210), 15:30-16:00 -> (390,420)
# Amber: 9:00-9:30 -> (0,30), 10:00-10:30 -> (60,90), 11:30-12:00 -> (150,180),
#        12:30-14:00 -> (210,300), 14:30-15:00 -> (330,360), 15:30-17:00 -> (390,480)
monday_busy = [
    (0, 30),    # Amber
    (60, 90),   # Amber
    (90, 120),  # Ronald
    (150, 180), # Amber
    (180, 210), # Ronald
    (210, 300), # Amber
    (330, 360), # Amber
    (390, 420), # Ronald
    (390, 480)  # Amber
]

# Tuesday busy intervals:
# Ronald: 9:00-9:30 -> (0,30), 12:00-12:30 -> (180,210), 15:30-16:30 -> (390,450)
# Amber: 9:00-9:30 -> (0,30), 10:00-11:30 -> (60,150), 12:00-12:30 -> (180,210),
#        13:30-15:30 -> (270,390), 16:30-17:00 -> (450,480)
tuesday_busy = [
    (0, 30),
    (60, 150),
    (180, 210),
    (270, 390),
    (390, 450),
    (450, 480)
]

# Wednesday busy intervals:
# Ronald: 9:30-10:30 -> (30,90), 11:00-12:00 -> (120,180), 12:30-13:00 -> (210,240),
#         13:30-14:00 -> (270,300), 16:30-17:00 -> (450,480)
# Amber: 9:00-9:30 -> (0,30), 10:00-10:30 -> (60,90), 11:00-13:30 -> (120,270),
#        15:00-15:30 -> (360,390)
wednesday_busy = [
    (0, 30),    # Amber
    (30, 90),   # Ronald
    (60, 90),   # Amber
    (120, 180), # Ronald
    (120, 270), # Amber
    (210, 240), # Ronald
    (270, 300), # Ronald
    (360, 390), # Amber
    (450, 480)  # Ronald
]

# Helper function: no overlap between meeting [start, start+duration) and a busy interval (bs, be)
def non_overlap_constraint(meeting_start, busy_interval):
    bs, be = busy_interval
    # The meeting is either completely before the busy interval or completely after.
    return Or(meeting_start + meeting_duration <= bs, meeting_start >= be)

# For each day, if the meeting is scheduled on that day, then it must not overlap with any busy interval.
for (bs, be) in monday_busy:
    opt.add(Implies(day == 0, non_overlap_constraint(start, (bs, be))))
for (bs, be) in tuesday_busy:
    opt.add(Implies(day == 1, non_overlap_constraint(start, (bs, be))))
for (bs, be) in wednesday_busy:
    opt.add(Implies(day == 2, non_overlap_constraint(start, (bs, be))))

# To choose the earliest possible meeting time (by day and by start time), define an objective.
# We use a combined metric: Monday (day=0) is the earliest, then Tuesday (day=1), then Wednesday (day=2).
# Multiplying day by a large constant ensures that any available Monday time is better than Tuesday.
objective = day * 10000 + start
opt.minimize(objective)

# Check if a solution exists and output the meeting day and time in the format HH:MM:HH:MM.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[day].as_long()
    chosen_start = model[start].as_long()
    chosen_end = chosen_start + meeting_duration
    
    # Convert from minutes offset to clock time (workday starts at 9:00).
    start_hour = 9 + chosen_start // 60
    start_min = chosen_start % 60
    end_hour = 9 + chosen_end // 60
    end_min = chosen_end % 60
    
    # Format the times with leading zeros.
    start_time_str = f"{start_hour:02d}:{start_min:02d}"
    end_time_str = f"{end_hour:02d}:{end_min:02d}"
    
    # Map the numeric day to the day name.
    days = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    
    # Output in the format "Day HH:MM:HH:MM"
    print(f"{days[chosen_day]} {start_time_str}:{end_time_str}")
else:
    print("No valid meeting time found.")