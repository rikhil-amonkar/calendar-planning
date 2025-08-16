from z3 import *

# Helper function to convert minutes (offset from 9:00) to HH:MM format (24-hour)
def minutes_to_time(minutes):
    hour = 9 + minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Create the Z3 solver instance
solver = Solver()

# Use an integer variable "day" to represent Monday (0) or Tuesday (1)
day = Int('day')
# "start" is the meeting start time in minutes after 9:00.
start = Int('start')
duration = 30
finish = start + duration

# The day must be either Monday (0) or Tuesday (1)
solver.add(Or(day == 0, day == 1))

# Depending on the day, the meeting must finish during working hours.
# For Monday, work hours are 9:00-17:00 so finish <= 480 (minutes after 9:00).
# For Tuesday, Lawrence cannot meet after 16:30, so finish <= 450.
solver.add(If(day == 0, And(start >= 0, finish <= 480),
              And(start >= 0, finish <= 450)))

# -------------------------------------------------------------------
# Participant busy schedules are provided as intervals (in minutes offset from 9:00).
#
# Jesse's busy slots:
#    Monday:    13:30-14:00  -> [270, 300]
#               14:30-15:00  -> [330, 360]
#    Tuesday:    9:00-9:30   -> [0, 30]
#               13:00-13:30  -> [240, 270]
#               14:00-15:00  -> [300, 360]
#
# Lawrence's busy slots:
#    Monday:    9:00-17:00   -> [0, 480]
#    Tuesday:   9:30-10:30  -> [30, 90]
#               11:30-12:30 -> [150, 210]
#               13:00-13:30 -> [240, 270]
#               14:30-15:00 -> [330, 360]
#               15:30-16:30 -> [390, 450]
#
# For each busy interval, the meeting (from start to finish) must not overlap.
# That is, for each busy interval [a, b] we need:
#     finish <= a   OR   start >= b
# -------------------------------------------------------------------

# Constraint for Jesse's schedule
jesse_busy_monday = And(Or(finish <= 270, start >= 300),  # [13:30, 14:00]
                         Or(finish <= 330, start >= 360))  # [14:30, 15:00]
jesse_busy_tuesday = And(Or(finish <= 0,   start >= 30),   # [9:00, 9:30]
                          Or(finish <= 240, start >= 270),     # [13:00, 13:30]
                          Or(finish <= 300, start >= 360))       # [14:00, 15:00]

solver.add(If(day == 0, jesse_busy_monday, jesse_busy_tuesday))

# Constraint for Lawrence's schedule
# Note: On Monday, Lawrence is busy the entire day, so no meeting is possible.
# We express this as a constraint that immediately makes Monday infeasible.
lawrence_busy_monday = Or(finish <= 0, start >= 480)  # (No valid start exists in [0,450])
lawrence_busy_tuesday = And(Or(finish <= 30,  start >= 90),     # [9:30, 10:30]
                            Or(finish <= 150, start >= 210),    # [11:30, 12:30]
                            Or(finish <= 240, start >= 270),    # [13:00, 13:30]
                            Or(finish <= 330, start >= 360),    # [14:30, 15:00]
                            Or(finish <= 390, start >= 450))    # [15:30, 16:30]

solver.add(If(day == 0, lawrence_busy_monday, lawrence_busy_tuesday))

# Because Monday is entirely blocked for Lawrence, force the meeting to be on Tuesday.
solver.add(day == 1)

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    sol_day = model[day].as_long()    # Will be 1 meaning Tuesday.
    sol_start = model[start].as_long()
    sol_finish = sol_start + duration

    # Convert the meeting start and finish times (which are minutes after 9:00) to HH:MM.
    start_time = minutes_to_time(sol_start)
    finish_time = minutes_to_time(sol_finish)
    day_str = "Monday" if sol_day == 0 else "Tuesday"

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", start_time)
    print("End Time:", finish_time)
else:
    print("No solution found")