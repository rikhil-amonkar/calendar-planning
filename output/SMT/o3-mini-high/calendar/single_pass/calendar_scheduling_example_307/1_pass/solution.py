from z3 import *

# The meeting lasts 30 minutes.
duration = 30

# Let s be the number of minutes after 9:00 when the meeting starts.
s = Int('s')

solver = Solver()

# Working hours: meeting must be between 9:00 and 17:00,
# so s must be at least 0 and s+duration <= 480 (since 17:00 is 480 minutes after 9:00).
solver.add(s >= 0, s + duration <= 480)

# For each busy interval [a, b] (in minutes after 9:00),
# add: either the meeting ends on or before a (s+duration <= a) or it starts on or after b (s >= b).

# Stephen is busy:
# 10:00-10:30  -> [60, 90]
solver.add(Or(s + duration <= 60, s >= 90))
# 12:00-12:30  -> [180, 210]
solver.add(Or(s + duration <= 180, s >= 210))

# Brittany is busy:
# 11:00-11:30  -> [120, 150]
solver.add(Or(s + duration <= 120, s >= 150))
# 13:30-14:00  -> [270, 300]
solver.add(Or(s + duration <= 270, s >= 300))
# 15:30-16:00  -> [390, 420]
solver.add(Or(s + duration <= 390, s >= 420))
# 16:30-17:00  -> [450, 480]
solver.add(Or(s + duration <= 450, s >= 480))

# Dorothy is busy:
# 9:00-9:30   -> [0, 30]   (Since s+duration <= 0 is impossible, we require s >= 30)
solver.add(s >= 30)
# 10:00-10:30 -> [60, 90]
solver.add(Or(s + duration <= 60, s >= 90))
# 11:00-12:30 -> [120, 210]
solver.add(Or(s + duration <= 120, s >= 210))
# 13:00-15:00 -> [240, 360] (s+duration <= 240 or s >= 360)
solver.add(Or(s + duration <= 240, s >= 360))
# 15:30-17:00 -> [390, 480]
solver.add(Or(s + duration <= 390, s >= 480))

# Rebecca is busy:
# 9:30-10:30  -> [30, 90]
solver.add(Or(s + duration <= 30, s >= 90))  # effectively forces s >= 90.
# 11:00-11:30 -> [120, 150]
solver.add(Or(s + duration <= 120, s >= 150))
# 12:00-12:30 -> [180, 210]
solver.add(Or(s + duration <= 180, s >= 210))
# 13:00-17:00 -> [240, 480]
solver.add(Or(s + duration <= 240, s >= 480))

# Jordan is busy:
# 9:00-9:30   -> [0, 30]
solver.add(s >= 30)
# 10:00-11:00 -> [60, 120]
solver.add(Or(s + duration <= 60, s >= 120))
# 11:30-12:00 -> [150, 180]
solver.add(Or(s + duration <= 150, s >= 180))
# 13:00-15:00 -> [240, 360]
solver.add(Or(s + duration <= 240, s >= 360))
# 15:30-16:30 -> [390, 450]
solver.add(Or(s + duration <= 390, s >= 450))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    start_offset = model[s].as_long()  # Minutes after 9:00 when meeting starts.
    
    # For clarity, note that:
    # 9:00 plus start_offset minutes gives the meeting start time,
    # and meeting end time is (start_offset + duration) minutes after 9:00.
    start_total = 9 * 60 + start_offset
    end_total = start_total + duration

    # Convert times to HH:MM in 24-hour format.
    start_hour = start_total // 60
    start_min = start_total % 60
    end_hour = end_total // 60
    end_min = end_total % 60

    start_time_str = f"{start_hour:02d}:{start_min:02d}"
    end_time_str = f"{end_hour:02d}:{end_min:02d}"

    # The meeting is scheduled on Monday.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution found.")