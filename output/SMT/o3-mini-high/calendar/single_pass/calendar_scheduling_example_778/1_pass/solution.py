from z3 import Solver, Int, Or, Implies, sat

# Create a solver instance.
solver = Solver()

# Define variables:
# "day" is an integer where 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# "start" is the meeting start time in minutes after 9:00.
day = Int('day')
start = Int('start')
duration = 30           # meeting duration in minutes
meeting_end = start + duration

# Allowed days: Monday, Tuesday, or Wednesday.
solver.add(Or(day == 0, day == 1, day == 2))

# Susan would rather not meet on Tuesday, so exclude day 1.
solver.add(day != 1)

# Meeting must occur during work hours 9:00 to 17:00.
# This means start >= 0 and meeting_end <= 480 (since 17:00 is 480 minutes after 9:00).
solver.add(start >= 0, meeting_end <= 480)

# --------------------------
# Monday (day==0) constraints:
# --------------------------
# Additional constraint for Sandra on Monday: she cannot meet after 16:00.
# Since meeting_end = start + 30, if day == 0 then meeting_end must be at most 420 (i.e. meeting finishes by 16:00).
solver.add(Implies(day == 0, meeting_end <= 420))

# Susan’s blocked times on Monday:
#   • 12:30 to 13:00 corresponds to minutes [210,240].
#   • 13:30 to 14:00 corresponds to minutes [270,300].
solver.add(Implies(day == 0, Or(meeting_end <= 210, start >= 240)))
solver.add(Implies(day == 0, Or(meeting_end <= 270, start >= 300)))

# Sandra’s blocked times on Monday:
#   • 9:00 to 13:00 → minutes [0,240]. (Meeting must start at or after 240.)
#   • 14:00 to 15:00 → minutes [300,360] (Meeting must finish by 300 or start at/after 360.)
#   • 16:00 to 16:30 is already ruled out by meeting_end <= 420.
solver.add(Implies(day == 0, start >= 240))
solver.add(Implies(day == 0, Or(meeting_end <= 300, start >= 360)))

# -----------------------------
# Wednesday (day==2) constraints:
# -----------------------------
# Susan’s blocked times on Wednesday:
#   • 9:30 to 10:30 → minutes [30,90].
#   • 14:00 to 14:30 → minutes [300,330].
#   • 15:30 to 16:30 → minutes [390,450].
solver.add(Implies(day == 2, Or(meeting_end <= 30, start >= 90)))
solver.add(Implies(day == 2, Or(meeting_end <= 300, start >= 330)))
solver.add(Implies(day == 2, Or(meeting_end <= 390, start >= 450)))

# Sandra’s blocked times on Wednesday:
#   • 9:00 to 11:30 → minutes [0,150] so meeting must start at/after 150.
#   • 12:00 to 12:30 → minutes [180,210] i.e. either meeting ends by 180 or starts at/after 210.
#   • 13:00 to 17:00 → minutes [240,480] so the meeting must finish by 240.
solver.add(Implies(day == 2, start >= 150))
solver.add(Implies(day == 2, Or(meeting_end <= 180, start >= 210)))
solver.add(Implies(day == 2, meeting_end <= 240))

# -----------------------------
# (We are not modelling Tuesday because Susan prefers to avoid it.)
# -----------------------------

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + duration

    # Convert minutes-after-9:00 to a proper HH:MM string (24-hour clock).
    def format_time(minutes_from_9):
        total_minutes = minutes_from_9 + 9 * 60
        hour = total_minutes // 60
        minute = total_minutes % 60
        return "{:02d}:{:02d}".format(hour, minute)

    # Map day value to its name.
    day_name = "Monday" if day_val == 0 else "Tuesday" if day_val == 1 else "Wednesday"

    # Print the solution in the specified format.
    print("SOLUTION:")
    print("Day: " + day_name)
    print("Start Time: " + format_time(start_val))
    print("End Time: " + format_time(end_val))
else:
    print("No valid meeting time found.")