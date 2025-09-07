from z3 import *

# Meeting duration (in minutes)
DURATION = 60

# Create integer variables:
# meeting_day: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
# meeting_start: start time in minutes from midnight
meeting_day = Int("meeting_day")
meeting_start = Int("meeting_start")

# Create a solver
solver = Solver()

# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes); thus meeting must start at or after 540 
# and finish by 1020, so meeting_start <= 1020 - DURATION.
solver.add(meeting_day >= 0, meeting_day <= 3)
solver.add(meeting_start >= 540, meeting_start <= 1020 - DURATION)

# For a meeting time [meeting_start, meeting_start + DURATION) on a given day,
# it must not overlap any busy interval. Two intervals [a,b) and [c,d) do not overlap
# if b <= c or a >= d.

# Monday constraints (meeting_day == 0)
# Megan is busy on Monday: [13:00,13:30] (780,810) and [14:00,15:30] (840,930)
# Daniel is busy on Monday: [10:00,11:30] (600,690) and [12:30,15:00] (750,900)
monday_busy = [(780, 810), (840, 930), (600, 690), (750, 900)]
for busy_start, busy_end in monday_busy:
    solver.add(Implies(meeting_day == 0,
                       Or(meeting_start + DURATION <= busy_start,
                          meeting_start >= busy_end)))

# Tuesday constraints (meeting_day == 1)
# Megan is busy on Tuesday: [9:00,9:30] (540,570), [12:00,12:30] (720,750), [16:00,17:00] (960,1020)
# Daniel is busy on Tuesday: [9:00,10:00] (540,600) and [10:30,17:00] (630,1020)
tuesday_busy = [(540, 570), (720, 750), (960, 1020), (540, 600), (630, 1020)]
for busy_start, busy_end in tuesday_busy:
    solver.add(Implies(meeting_day == 1,
                       Or(meeting_start + DURATION <= busy_start,
                          meeting_start >= busy_end)))

# Wednesday constraints (meeting_day == 2)
# Megan is busy on Wednesday: [9:30,10:00] (570,600), [10:30,11:30] (630,690), 
#                         [12:30,14:00] (750,840), [16:00,16:30] (960,990)
# Daniel is busy on Wednesday: [9:00,10:00] (540,600), [10:30,11:30] (630,690), [12:00,17:00] (720,1020)
wednesday_busy = [(570, 600), (630, 690), (750, 840), (960, 990),
                   (540, 600), (630, 690), (720, 1020)]
for busy_start, busy_end in wednesday_busy:
    solver.add(Implies(meeting_day == 2,
                       Or(meeting_start + DURATION <= busy_start,
                          meeting_start >= busy_end)))

# Thursday constraints (meeting_day == 3)
# Megan is busy on Thursday: [13:30,14:30] (810,870) and [15:00,15:30] (900,930)
# Daniel is busy on Thursday: [9:00,12:00] (540,720), [12:30,14:30] (750,870),
#                            [15:00,15:30] (900,930), [16:00,17:00] (960,1020)
thursday_busy = [(810, 870), (900, 930),
                 (540, 720), (750, 870), (900, 930), (960, 1020)]
for busy_start, busy_end in thursday_busy:
    solver.add(Implies(meeting_day == 3,
                       Or(meeting_start + DURATION <= busy_start,
                          meeting_start >= busy_end)))

# Use an Optimize object to choose the earliest available meeting time.
# We want to minimize the day and then the start time.
opt = Optimize()
# Add all the constraints from the solver.
for c in solver.assertions():
    opt.add(c)

# Create a combined objective: meeting_day is prioritized over meeting_start.
# Multiplying meeting_day by a large constant ensures preference of an earlier day.
opt.minimize(meeting_day * 10000 + meeting_start)

if opt.check() == sat:
    model = opt.model()
    day_val = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + DURATION

    # Helper to convert minutes to HH:MM
    def minutes_to_str(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    chosen_day = day_names[day_val]
    meeting_time = f"{minutes_to_str(start_val)}:{minutes_to_str(end_val)}"
    print(f"{chosen_day} {meeting_time}")
else:
    print("No valid meeting time found.")