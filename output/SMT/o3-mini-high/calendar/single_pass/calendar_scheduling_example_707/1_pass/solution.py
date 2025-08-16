from z3 import *

# We'll represent days as integers:
# 0: Monday, 1: Tuesday, 2: Wednesday
# But note that Ryan cannot meet on Wednesday so our domain will effectively be {0,1}.

# Helper to convert minutes past midnight to HH:MM string.
def minutes_to_str(m):
    hrs = m // 60
    mins = m % 60
    return f"{hrs:02d}:{mins:02d}"

# Create a Z3 solver instance.
s = Solver()

# Define our decision variables.
day = Int('day')      # day: 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
start = Int('start')  # meeting start time in minutes past midnight

meeting_duration = 30
meeting_end = start + meeting_duration

# Restrict day to Monday or Tuesday.
s.add(Or(day == 0, day == 1))
# (Alternatively, you could allow all three days then later add s.add(day != 2) because Ryan can't do Wednesday.)

# Working hours: meeting must start no earlier than 9:00 (540 minutes)
# and finish by 17:00 (1020 minutes).
s.add(start >= 540, meeting_end <= 1020)

# For each busy interval, we require that the meeting does not overlap.
# That is, for a busy interval [busy_start, busy_end], we need:
#   meeting_end <= busy_start   OR   start >= busy_end

# ----- Monday constraints (day == 0) -----
# Ryan's meetings on Monday (in minutes):
#   9:30-10:00 --> [570,600]
#   11:00-12:00 --> [660,720]
#   13:00-13:30 --> [780,810]
#   15:30-16:00 --> [930,960]
monday_busy_ryan = [(570, 600), (660, 720), (780, 810), (930, 960)]

# Adam's meetings on Monday:
#   9:00-10:30 --> [540,630]
#   11:00-13:30 --> [660,810]
#   14:00-16:00 --> [840,960]
#   16:30-17:00 --> [990,1020]
monday_busy_adam = [(540, 630), (660, 810), (840, 960), (990, 1020)]

monday_constraints = []

# For every busy interval on Monday, the meeting must not overlap.
for (bstart, bend) in monday_busy_ryan:
    monday_constraints.append(Or(meeting_end <= bstart, start >= bend))
for (bstart, bend) in monday_busy_adam:
    monday_constraints.append(Or(meeting_end <= bstart, start >= bend))

# Adam's preference: on Monday he would like to avoid meetings before 14:30 (870 minutes).
monday_constraints.append(start >= 870)

s.add(Implies(day == 0, And(monday_constraints)))

# ----- Tuesday constraints (day == 1) -----
# Ryan's meetings on Tuesday:
#   11:30-12:30 --> [690,750]
#   15:30-16:00 --> [930,960]
tuesday_busy_ryan = [(690, 750), (930, 960)]

# Adam's meetings on Tuesday:
#   9:00-10:00   --> [540,600]
#   10:30-15:30  --> [630,930]
#   16:00-17:00  --> [960,1020]
tuesday_busy_adam = [(540, 600), (630, 930), (960, 1020)]

tuesday_constraints = []
for (bstart, bend) in tuesday_busy_ryan:
    tuesday_constraints.append(Or(meeting_end <= bstart, start >= bend))
for (bstart, bend) in tuesday_busy_adam:
    tuesday_constraints.append(Or(meeting_end <= bstart, start >= bend))

s.add(Implies(day == 1, And(tuesday_constraints)))

# (Although Wednesday busy times exist as well, Ryan is not available on Wednesday.)

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    chosen_day = m[day].as_long()
    chosen_start = m[start].as_long()
    chosen_end = chosen_start + meeting_duration

    # Map our integer day to its string representation.
    day_dict = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    # Prepare the output in the required format.
    print("SOLUTION:")
    print("Day: " + day_dict[chosen_day])
    print("Start Time: " + minutes_to_str(chosen_start))
    print("End Time: " + minutes_to_str(chosen_end))
else:
    print("No solution found.")