from z3 import *

# We represent the meeting day as an integer where:
#   0 = Monday
#   1 = Tuesday
# The meeting start time is represented as the number of minutes after 9:00.
# Because the work day is 9:00 to 17:00 (8 hours = 480 minutes) and the meeting lasts 60 minutes,
# valid start times lie in the interval [0, 420].

# Create Z3 solver instance
solver = Solver()

# Declare variables:
day = Int('day')       # 0: Monday, 1: Tuesday
start = Int('start')   # Start time in minutes offset from 9:00
duration = 60         # meeting duration in minutes
end = start + duration

# Domain constraints:
solver.add(Or(day == 0, day == 1))
solver.add(start >= 0, start <= 420)  # meeting must finish by 17:00

# Helper: non-overlap constraint between meeting [start, start+duration)
# and a busy interval [busy_start, busy_end) 
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Define the busy intervals (in minutes from 9:00) for each person.

# Russell's schedule:
# Monday: busy 10:30 to 11:00    => 10:30 = 90 minutes, 11:00 = 120 minutes
# Tuesday: busy 13:00 to 13:30   => 13:00 = 240 minutes, 13:30 = 270 minutes
# Preference: Russell "would rather not" meet on Tuesday before 13:30 (i.e. before 270 minutes)
#   For our purposes we add a constraint that if the meeting is on Tuesday, then it starts no earlier than 13:30.
russell_busy_monday = [(90, 120)]
russell_busy_tuesday = [(240, 270)]  # plus the preference s >= 270 if Tuesday

# Alexander's schedule:
# Monday: busy 9:00 to 11:30, 12:00 to 14:30, 15:00 to 17:00
#   => 9:00-11:30: [0, 150) because 11:30 is 2.5 hours after 9:00 (150 minutes)
#      12:00-14:30: [180, 330)
#      15:00-17:00: [360, 480)
alex_busy_monday = [(0, 150), (180, 330), (360, 480)]

# Tuesday: busy 9:00 to 10:00, 13:00 to 14:00, 15:00 to 15:30, 16:00 to 16:30
#   => 9:00-10:00: [0, 60)
#      13:00-14:00: [240, 300)
#      15:00-15:30: [360, 390)
#      16:00-16:30: [420, 450)
alex_busy_tuesday = [(0, 60), (240, 300), (360, 390), (420, 450)]

# --- Add constraints for Monday (day == 0) ---
# Russell on Monday:
for (b_start, b_end) in russell_busy_monday:
    solver.add(Implies(day == 0, no_overlap(start, duration, b_start, b_end)))
# Alexander on Monday:
for (b_start, b_end) in alex_busy_monday:
    solver.add(Implies(day == 0, no_overlap(start, duration, b_start, b_end)))

# --- Add constraints for Tuesday (day == 1) ---
# Russell's Tuesday constraints:
# (a) Busy interval: must not intersect [240, 270)
for (b_start, b_end) in russell_busy_tuesday:
    solver.add(Implies(day == 1, no_overlap(start, duration, b_start, b_end)))
# (b) Preference: would rather not meet before 13:30, so enforce start >= 270.
solver.add(Implies(day == 1, start >= 270))

# Alexander's Tuesday constraints:
for (b_start, b_end) in alex_busy_tuesday:
    solver.add(Implies(day == 1, no_overlap(start, duration, b_start, b_end)))

# ----- Analyze the constraints -----
# Notice: On Monday, Alexander’s busy intervals leave only two free slots (11:30-12:00 and 14:30-15:00)
# which are too short for a 60-minute meeting.
# On Tuesday, combining Russell's preference and Alexander's schedule forces the meeting into the free
# period after Alexander's morning meeting and after his busy block from 13:00 to 14:00.
# In fact, the constraint from Alexander's busy period [240,300) forces:
#    no_overlap(start,60,240,300)  => Either start+60 <= 240 or start >= 300.
# Given Russell's preference (start >= 270) the only possibility is start >= 300.
# Then, the free interval from 300 to (300+60=360) fits exactly into Alexander's free period before his next busy slot.
#
# Thus, the only solution is:
#    day = Tuesday  (i.e. day == 1)
#    start = 300 minutes after 9:00, i.e. 9:00 + 300 minutes = 14:00
#    end = 14:00 + 60 minutes = 15:00

# Solve the constraints:
if solver.check() == sat:
    m = solver.model()
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    
    # Convert day value to string:
    day_str = "Monday" if day_val == 0 else "Tuesday"
    
    # Convert start and end time (minutes offset from 9:00) to HH:MM format.
    meeting_start_total = start_val      # in minutes after 9:00
    meeting_end_total = start_val + duration
    
    # Calculate the actual time (adding to 9:00)
    start_hour = 9 + meeting_start_total // 60
    start_minute = meeting_start_total % 60
    end_hour = 9 + meeting_end_total // 60
    end_minute = meeting_end_total % 60
    
    start_time_str = f"{start_hour:02d}:{start_minute:02d}"
    end_time_str = f"{end_hour:02d}:{end_minute:02d}"
    
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution exists.")