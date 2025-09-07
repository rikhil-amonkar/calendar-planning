from z3 import *

# Create solver instance
s = Solver()

# Define variables:
# day: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday.
# start: meeting start time in minutes after 9:00. Since working hours are 9:00 to 17:00,
# and the meeting lasts 60 minutes, start can be between 0 and 420.
day = Int('day')
start = Int('start')

# The meeting interval is [start, start + 60]
s.add(Or(day == 0, day == 1, day == 2, day == 3))
s.add(start >= 0, start <= 420)

# A helper to enforce that the meeting [start, start+60] does not overlap a busy block [a, b]
def no_overlap(a, b):
    # Meeting ends before busy block starts OR starts after busy block ends.
    return Or(start + 60 <= a, start >= b)

# -- Monday constraints (day == 0) --
# Convert booked times to minutes after 9:00.
# Natalie is busy:
natalie_mon = [(0, 30), (60, 180), (210, 240), (300, 330), (360, 450)]
# William is busy:
william_mon = [(30, 120), (150, 480)]

for (a, b) in natalie_mon:
    s.add(Implies(day == 0, no_overlap(a, b)))
for (a, b) in william_mon:
    s.add(Implies(day == 0, no_overlap(a, b)))

# -- Tuesday constraints (day == 1) --
# Natalie:
natalie_tue = [(0, 30), (60, 90), (210, 300), (420, 480)]
# William:
william_tue = [(0, 240), (270, 420)]

for (a, b) in natalie_tue:
    s.add(Implies(day == 1, no_overlap(a, b)))
for (a, b) in william_tue:
    s.add(Implies(day == 1, no_overlap(a, b)))

# -- Wednesday constraints (day == 2) --
# Natalie:
natalie_wed = [(120, 150), (420, 450)]
# William:
william_wed = [(0, 210), (240, 330), (390, 420), (450, 480)]

for (a, b) in natalie_wed:
    s.add(Implies(day == 2, no_overlap(a, b)))
for (a, b) in william_wed:
    s.add(Implies(day == 2, no_overlap(a, b)))

# -- Thursday constraints (day == 3) --
# Natalie:
natalie_thu = [(60, 120), (150, 360), (390, 420), (450, 480)]
# William:
william_thu = [(0, 90), (120, 150), (180, 210), (240, 300), (360, 480)]

for (a, b) in natalie_thu:
    s.add(Implies(day == 3, no_overlap(a, b)))
for (a, b) in william_thu:
    s.add(Implies(day == 3, no_overlap(a, b)))

# Solve for a valid meeting time
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    
    # Convert chosen day to its name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_name = days[chosen_day]
    
    # Given the meeting start (in minutes after 9:00), convert it to absolute minutes.
    meeting_start_minutes = 540 + chosen_start  # 9:00 is 540 minutes after midnight.
    meeting_end_minutes = meeting_start_minutes + 60
    
    # A helper function to format minutes as HH:MM.
    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    meeting_start_str = format_time(meeting_start_minutes)
    meeting_end_str = format_time(meeting_end_minutes)
    
    print(f"{day_name} {meeting_start_str}:{meeting_end_str}")
else:
    print("No solution found.")