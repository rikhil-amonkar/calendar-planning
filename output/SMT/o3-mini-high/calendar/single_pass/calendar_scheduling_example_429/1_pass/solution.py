from z3 import *

# Meeting duration in minutes
duration = 30

# We measure time as minutes after 9:00.
# Working hours: from 9:00 (0 minutes) to 17:00 (480 minutes).
# Thus the meeting’s start time "t" must satisfy t >= 0 and t + duration <= 480.
t = Int('t')

solver = Solver()

# Base working hours constraints
solver.add(t >= 0, t + duration <= 480)

# A helper to add a no-overlap constraint: the meeting [t, t+duration)
# must either end at or before a busy interval starts OR start at or after it ends.
def no_overlap(t, busy_start, busy_end, duration):
    return Or(t + duration <= busy_start, t >= busy_end)

# Busy intervals for each participant are given as (start, end) minutes from 9:00.

# Judy: [13:00,13:30] and [16:00,16:30]
# 13:00 -> 240; 13:30 -> 270; 16:00 -> 420; 16:30 -> 450
judy_busy = [(240, 270), (420, 450)]

# Olivia: [10:00,10:30], [12:00,13:00], [14:00,14:30]
# 10:00 -> 60; 10:30 -> 90; 12:00 -> 180; 13:00 -> 240; 14:00 -> 300; 14:30 -> 330
olivia_busy = [(60, 90), (180, 240), (300, 330)]

# Eric: free all day, so no busy intervals.
eric_busy = []

# Jacqueline: [10:00,10:30], [15:00,15:30]
# 10:00 -> 60; 10:30 -> 90; 15:00 -> 360; 15:30 -> 390
jacqueline_busy = [(60, 90), (360, 390)]

# Laura: [9:00,10:00], [10:30,12:00], [13:00,13:30], [14:30,15:00], [15:30,17:00]
# 9:00 -> 0; 10:00 -> 60; 10:30 -> 90; 12:00 -> 180; 13:00 -> 240; 13:30 -> 270;
# 14:30 -> 330; 15:00 -> 360; 15:30 -> 390; 17:00 -> 480
laura_busy = [(0, 60), (90, 180), (240, 270), (330, 360), (390, 480)]

# Tyler: [9:00,10:00], [11:00,11:30], [12:30,13:00], [14:00,14:30], [15:30,17:00]
# 9:00 -> 0; 10:00 -> 60; 11:00 -> 120; 11:30 -> 150; 12:30 -> 210; 13:00 -> 240;
# 14:00 -> 300; 14:30 -> 330; 15:30 -> 390; 17:00 -> 480
tyler_busy = [(0, 60), (120, 150), (210, 240), (300, 330), (390, 480)]

# Lisa: [9:30,10:30], [11:00,11:30], [12:00,12:30], [13:00,13:30], [14:00,14:30], [16:00,17:00]
# 9:30 -> 30; 10:30 -> 90; 11:00 -> 120; 11:30 -> 150; 12:00 -> 180; 12:30 -> 210;
# 13:00 -> 240; 13:30 -> 270; 14:00 -> 300; 14:30 -> 330; 16:00 -> 420; 17:00 -> 480
lisa_busy = [(30, 90), (120, 150), (180, 210), (240, 270), (300, 330), (420, 480)]

# Combine all busy intervals
all_busy_intervals = judy_busy + olivia_busy + eric_busy + jacqueline_busy + laura_busy + tyler_busy + lisa_busy

# Add non-overlap constraints for the meeting for every busy interval.
for busy_start, busy_end in all_busy_intervals:
    solver.add(no_overlap(t, busy_start, busy_end, duration))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    start_val = model[t].as_long()  # in minutes after 9:00
    end_val = start_val + duration
    
    # Convert minutes into HH:MM (24-hour format) by adding to 9:00.
    start_hour = 9 + start_val // 60
    start_min = start_val % 60
    end_hour = 9 + end_val // 60
    end_min = end_val % 60

    # Format the solution output as specified.
    solution = f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02d}:{start_min:02d}\nEnd Time: {end_hour:02d}:{end_min:02d}"
    print(solution)
else:
    print("No solution found.")