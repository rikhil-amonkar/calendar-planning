from z3 import Solver, Int, Or

# Represent time in minutes from midnight (e.g., 9:00 = 540, 17:00 = 1020, 11:00 = 660)
meeting_duration = 30
working_start = 9 * 60    # 540
working_end = 17 * 60     # 1020
latest_meeting_end_for_albert = 11 * 60  # 660

# Busy intervals for Albert (in minutes)
# Albert is busy:
#   9:00 to 10:00  -> [540, 600]
#   10:30 to 12:00 -> [630, 720]
#   15:00 to 16:30 -> [900, 990] (this one is irrelevant because Albert cannot meet after 11:00)
busy1_start, busy1_end = 9 * 60, 10 * 60   # 540, 600
busy2_start, busy2_end = 10 * 60 + 30, 12 * 60  # 630, 720

# We create a solver instance.
s = Solver()

# Define variable for the meeting start time (in minutes from midnight)
start = Int('start')
end = start + meeting_duration

# Meeting must be during working hours.
s.add(start >= working_start)
s.add(end <= working_end)

# Albert cannot meet after 11:00, so the meeting must finish by 11:00.
s.add(end <= latest_meeting_end_for_albert)

# Deborah is free all day, so no additional constraint from Deborah.

# Avoid Albert's busy intervals.
# For busy interval 1: meeting should not overlap with [busy1_start, busy1_end]
# Since the meeting is within working hours (>=540), the only option is to start after busy1 ends.
s.add(start >= busy1_end)

# For busy interval 2: meeting should not overlap with [busy2_start, busy2_end]
# The meeting must either finish before busy2 starts or start after busy2 ends.
# Given that meeting must finish by 11:00 (660 minutes) and busy2 starts at 630,
# the only feasible option is to finish before busy2 starts.
s.add(end <= busy2_start)

# Now check for a solution.
if s.check().r == 1:  # sat
    model = s.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration
    
    # Convert minutes to HH:MM (24-hour format)
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    day = "Monday"
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    
    # Print the solution in the required format:
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found.")