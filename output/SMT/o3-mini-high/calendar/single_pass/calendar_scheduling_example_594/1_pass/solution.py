from z3 import Optimize

# We represent time in minutes since midnight.
# Define the working day: 9:00 (540 minutes) to 17:00 (1020 minutes).
work_start = 9 * 60    # 540
work_end = 17 * 60     # 1020
meeting_duration = 30  # Meeting duration in minutes

# Create an Optimize object to allow us to minimize the starting time.
opt = Optimize()

# Meeting start time variable (in minutes)
t = opt.int_val(0)  # declare t as an integer variable
t = opt.int('t')

# Meeting must be within the working day.
opt.add(t >= work_start)
opt.add(t + meeting_duration <= work_end)

# Define the busy intervals (in minutes since midnight) for both participants.
# Adam's busy intervals:
#   9:30 - 10:00  -> (570, 600)
#   12:30 - 13:00 -> (750, 780)
#   14:30 - 15:00 -> (870, 900)
#   16:30 - 17:00 -> (990, 1020)
# Roy's busy intervals:
#   10:00 - 11:00 -> (600, 660)
#   11:30 - 13:00 -> (690, 780)
#   13:30 - 14:30 -> (810, 870)
#   16:30 - 17:00 -> (990, 1020)
busy_intervals = [
    (570, 600),   # Adam
    (750, 780),   # Adam
    (870, 900),   # Adam
    (990, 1020),  # Adam
    (600, 660),   # Roy
    (690, 780),   # Roy
    (810, 870),   # Roy
    (990, 1020)   # Roy
]

# For each busy interval, ensure the meeting does not overlap with it.
# That is, for each busy interval [b_start, b_end), we must have either:
#   meeting_end <= b_start   OR   t >= b_end.
for b_start, b_end in busy_intervals:
    opt.add( (t + meeting_duration <= b_start) | (t >= b_end) )

# Set the objective to minimize the start time (i.e. the earliest possible meeting).
opt.minimize(t)

# Check for a solution and extract it.
if opt.check() == sat:
    model = opt.model()
    meeting_start = model[t].as_long()
    meeting_end = meeting_start + meeting_duration

    # Helper function to convert minutes into HH:MM format.
    def minutes_to_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", minutes_to_time(meeting_start))
    print("End Time:", minutes_to_time(meeting_end))
else:
    print("No solution found.")