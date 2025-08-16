from z3 import *

# Define the solver
solver = Solver()

# We represent days as follows:
# 0 -> Monday, 1 -> Tuesday, 2 -> Wednesday
d = Int('d')
solver.add(Or(d == 0, d == 1, d == 2))  # meeting must be on Monday, Tuesday or Wednesday

# Meeting start time in minutes since midnight.
s = Int('s')
meeting_duration = 30
e = s + meeting_duration  # meeting end time

# Working hours: 09:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(s >= 540, e <= 1020)

# Cheryl cannot meet on Wednesday.
solver.add(d != 2)

# ---------------------------
# Busy intervals (in minutes) for each participant on each day.
# For Cheryl:
#   Monday busy intervals: [09:00,09:30] -> [540,570]
#                         [11:30,13:00] -> [690,780]
#                         [15:30,16:00] -> [930,960]
#   Tuesday busy interval: [15:00,15:30] -> [900,930]
cheryl_monday_busy = [(540, 570), (690, 780), (930, 960)]
for (b_start, b_end) in cheryl_monday_busy:
    solver.add(Implies(d == 0, Or(e <= b_start, s >= b_end)))

# Tuesday busy interval for Cheryl
solver.add(Implies(d == 1, Or(e <= 900, s >= 930)))

# For Kyle:
#   Monday busy interval: [09:00,17:00] -> [540,1020]
#   Tuesday busy interval: [09:30,17:00] -> [570,1020]
#   Wednesday busy intervals exist but Cheryl cannot meet on Wednesday, so we ignore that case.
solver.add(Implies(d == 0, Or(e <= 540, s >= 1020)))
solver.add(Implies(d == 1, Or(e <= 570, s >= 1020)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    day_val = model[d].as_long()
    s_val = model[s].as_long()
    e_val = s_val + meeting_duration

    # Mapping our integer day representation back to a day string.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    meeting_day = day_map[day_val]

    # Helper function: convert minutes to "HH:MM" format.
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Print the solution as required.
    print("SOLUTION:")
    print("Day:", meeting_day)
    print("Start Time:", format_time(s_val))
    print("End Time:", format_time(e_val))
else:
    print("No solution found.")