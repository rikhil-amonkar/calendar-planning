from z3 import Optimize, Int, Or, Implies, sat

# Define time boundaries (in minutes from midnight)
START_OF_DAY = 9 * 60   # 9:00 => 540
END_OF_DAY   = 17 * 60  # 17:00 => 1020
MEETING_DURATION = 60

# Create the optimizer (so we can minimize the meeting time)
opt = Optimize()

# Define variables:
# meeting_day: 0 for Monday, 1 for Tuesday, 2 for Wednesday
meeting_day = Int('meeting_day')
# meeting_start: the start time in minutes from midnight.
meeting_start = Int('meeting_start')
meeting_end = meeting_start + MEETING_DURATION

# Day domain constraint
opt.add(Or(meeting_day == 0, meeting_day == 1, meeting_day == 2))
# Meeting must lie within work hours.
opt.add(meeting_start >= START_OF_DAY)
opt.add(meeting_start <= END_OF_DAY - MEETING_DURATION)

# ---------------------------------------------------------------------
# Roy's busy schedule (in minutes from midnight)
#
# Monday busy intervals:
#   (10:00, 11:30) => (600, 690)
#   (12:00, 13:00) => (720, 780)
#   (14:00, 14:30) => (840, 870)
#   (15:00, 17:00) => (900, 1020)
#
# Tuesday busy intervals:
#   (10:30, 11:30) => (630, 690)
#   (12:00, 14:30) => (720, 870)
#   (15:00, 15:30) => (900, 930)
#   (16:00, 17:00) => (960, 1020)
#
# Wednesday busy intervals:
#   (9:30, 11:30)   => (570, 690)
#   (12:30, 14:00)  => (750, 840)
#   (14:30, 15:30)  => (870, 930)
#   (16:30, 17:00)  => (990, 1020)
# ---------------------------------------------------------------------

# For a meeting not to conflict with a busy interval, it must finish before that busy time
# starts OR start after that busy interval ends.
#
# Monday constraints (meeting_day == 0):
opt.add(Implies(meeting_day == 0, Or(meeting_end <= 600, meeting_start >= 690)))  # For (10:00,11:30)
opt.add(Implies(meeting_day == 0, Or(meeting_end <= 720, meeting_start >= 780)))  # For (12:00,13:00)
opt.add(Implies(meeting_day == 0, Or(meeting_end <= 840, meeting_start >= 870)))  # For (14:00,14:30)
# For (15:00,17:00), given the work hours meeting_start can't be after 17:00,
# we require the meeting to finish before 15:00.
opt.add(Implies(meeting_day == 0, meeting_end <= 900))  # 900 minutes = 15:00

# Tuesday constraints (meeting_day == 1):
opt.add(Implies(meeting_day == 1, Or(meeting_end <= 630, meeting_start >= 690)))  # For (10:30,11:30)
opt.add(Implies(meeting_day == 1, Or(meeting_end <= 720, meeting_start >= 870)))  # For (12:00,14:30)
opt.add(Implies(meeting_day == 1, Or(meeting_end <= 900, meeting_start >= 930)))  # For (15:00,15:30)
opt.add(Implies(meeting_day == 1, meeting_end <= 960))  # For (16:00,17:00): meeting must finish by 16:00

# Wednesday constraints (meeting_day == 2):
opt.add(Implies(meeting_day == 2, Or(meeting_end <= 570, meeting_start >= 690)))  # For (9:30,11:30)
opt.add(Implies(meeting_day == 2, Or(meeting_end <= 750, meeting_start >= 840)))  # For (12:30,14:00)
opt.add(Implies(meeting_day == 2, Or(meeting_end <= 870, meeting_start >= 930)))  # For (14:30,15:30)
opt.add(Implies(meeting_day == 2, meeting_end <= 990))  # For (16:30,17:00): meeting must finish by 16:30

# Preference: The group prefers to meet at the earliest availability.
# We create an objective that minimizes (meeting_day, meeting_start) in lexicographic order.
# To do this, we combine them into one objective value.
objective = meeting_day * 10000 + meeting_start
opt.minimize(objective)

# Solve the constraints.
if opt.check() == sat:
    model = opt.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + MEETING_DURATION

    # Map the day value to day name.
    day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_map[day_val]

    # Function to convert minutes since midnight to "HH:MM" format.
    def to_HHMM(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print("Day:", day_str)
    print("Start Time:", to_HHMM(start_val))
    print("End Time:", to_HHMM(end_val))
else:
    print("No solution found.")