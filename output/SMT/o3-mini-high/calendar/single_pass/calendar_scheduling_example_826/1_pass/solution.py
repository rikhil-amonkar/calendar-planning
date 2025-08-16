from z3 import Optimize, Int, Or, Implies

# Create an optimizer instance.
opt = Optimize()

# Define variables.
# We'll represent day as an integer:
# 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday, 3 -> Thursday
day = Int("day")
# meeting_start is the number of minutes after 9:00.
meeting_start = Int("meeting_start")
meeting_duration = 30
meeting_end = meeting_start + meeting_duration

# The meeting must start within work hours.
# Since work hours are 9:00 to 17:00 (480 minutes) and meeting is 30 minutes,
# meeting_start is in [0, 450] (0 means 9:00, 30 means 9:30, etc.).
opt.add(meeting_start >= 0, meeting_start <= 480 - meeting_duration)

# The meeting is to be scheduled on one of Monday, Tuesday, Wednesday, or Thursday.
opt.add( day >= 0, day <= 3 )
# Cheryl would rather not meet on Wednesday.
opt.add(day != 2)

# For each day, add constraints so that the meeting does not overlap with James' busy times.
# We assume that intervals that touch (meeting ends exactly at a busy meeting’s start,
# or meeting starts at a busy meeting’s end) are acceptable.

# Monday (day == 0):
# James is busy on Monday during:
# 9:00-9:30 -> [0, 30]
# 10:30-11:00 -> [90, 120]
# 12:30-13:00 -> [210, 240]
# 14:30-15:30 -> [330, 390]
# 16:30-17:00 -> [450, 480]
monday_busy = [
    Or(meeting_end <= 0,    meeting_start >= 30),
    Or(meeting_end <= 90,   meeting_start >= 120),
    Or(meeting_end <= 210,  meeting_start >= 240),
    Or(meeting_end <= 330,  meeting_start >= 390),
    Or(meeting_end <= 450,  meeting_start >= 480)
]
opt.add(Implies(day == 0,  # Monday
                monday_busy[0] and monday_busy[1] and monday_busy[2] and monday_busy[3] and monday_busy[4]))

# Tuesday (day == 1):
# James is busy on Tuesday during:
# 9:00-11:00 -> [0, 120]
# 11:30-12:00 -> [150, 180]
# 12:30-15:30 -> [210, 390]
# 16:00-17:00 -> [420, 480]
tuesday_busy = [
    Or(meeting_end <= 0,    meeting_start >= 120),
    Or(meeting_end <= 150,  meeting_start >= 180),
    Or(meeting_end <= 210,  meeting_start >= 390),
    Or(meeting_end <= 420,  meeting_start >= 480)
]
opt.add(Implies(day == 1, 
                tuesday_busy[0] and tuesday_busy[1] and tuesday_busy[2] and tuesday_busy[3]))

# Thursday (day == 3):
# James is busy on Thursday during:
# 9:30-11:30 -> [30, 150]
# 12:00-12:30 -> [180, 210]
# 13:00-13:30 -> [240, 270]
# 14:00-14:30 -> [300, 330]
# 16:30-17:00 -> [450, 480]
thursday_busy = [
    Or(meeting_end <= 30,  meeting_start >= 150),
    Or(meeting_end <= 180, meeting_start >= 210),
    Or(meeting_end <= 240, meeting_start >= 270),
    Or(meeting_end <= 300, meeting_start >= 330),
    Or(meeting_end <= 450, meeting_start >= 480)
]
opt.add(Implies(day == 3,
                thursday_busy[0] and thursday_busy[1] and thursday_busy[2] and thursday_busy[3] and thursday_busy[4]))

# Our goal is to schedule at the earliest availability.
# We want the meeting to be as early in the week as possible (Monday, then Tuesday, then Thursday)
# and as early on the day as possible.
h1 = opt.minimize(day)
h2 = opt.minimize(meeting_start)

# Find a solution.
if opt.check() == opt.sat:
    m = opt.model()
    day_val = m[day].as_long()
    start_val = m[meeting_start].as_long()
    
    # Map day numbers to names.
    day_names = { 0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday" }
    day_str = day_names[day_val]
    
    # Convert the meeting_start (minutes after 9:00) into a HH:MM time.
    start_hour = 9 + (start_val // 60)
    start_minute = start_val % 60
    start_time = f"{start_hour:02d}:{start_minute:02d}"
    
    # Compute meeting end time.
    end_val = start_val + meeting_duration
    end_hour = 9 + (end_val // 60)
    end_minute = end_val % 60
    end_time = f"{end_hour:02d}:{end_minute:02d}"
    
    # Print the required solution.
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", start_time)
    print("End Time:", end_time)
else:
    print("No solution found.")