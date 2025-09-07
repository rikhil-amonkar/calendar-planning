from z3 import Solver, Int, Or

# Convert minutes since midnight to HH:MM
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Duration of the meeting in minutes
MEETING_DURATION = 60

# Create an SMT solver instance
solver = Solver()

# Define an integer variable for meeting start time (in minutes since midnight)
meeting_start = Int("meeting_start")
meeting_end = meeting_start + MEETING_DURATION

# Working hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(meeting_start >= 540, meeting_end <= 1020)

# For each busy interval, we ensure that the meeting does NOT overlap it.
# The rule: For a busy interval [busy_start, busy_end],
# it must hold that either meeting_end <= busy_start OR meeting_start >= busy_end.

# Olivia's busy intervals:
# 12:30 to 13:30  -> [750, 810]
solver.add(Or(meeting_end <= 750, meeting_start >= 810))
# 14:30 to 15:00  -> [870, 900]
solver.add(Or(meeting_end <= 870, meeting_start >= 900))
# 16:30 to 17:00  -> [990, 1020]
solver.add(Or(meeting_end <= 990, meeting_start >= 1020))

# Anna has no meetings, so no constraints are added.

# Virginia's busy intervals:
# 9:00 to 10:00   -> [540, 600]
solver.add(Or(meeting_end <= 540, meeting_start >= 600))
# 11:30 to 16:00  -> [690, 960]
solver.add(Or(meeting_end <= 690, meeting_start >= 960))
# 16:30 to 17:00  -> [990, 1020]
solver.add(Or(meeting_end <= 990, meeting_start >= 1020))

# Paul's busy intervals:
# 9:00 to 9:30   -> [540, 570]
solver.add(Or(meeting_end <= 540, meeting_start >= 570))
# 11:00 to 11:30 -> [660, 690]
solver.add(Or(meeting_end <= 660, meeting_start >= 690))
# 13:00 to 14:00 -> [780, 840]
solver.add(Or(meeting_end <= 780, meeting_start >= 840))
# 14:30 to 16:00 -> [870, 960]
solver.add(Or(meeting_end <= 870, meeting_start >= 960))
# 16:30 to 17:00 -> [990, 1020]
solver.add(Or(meeting_end <= 990, meeting_start >= 1020))

if solver.check() == sat:
    model = solver.model()
    start_value = model[meeting_start].as_long()
    end_value = start_value + MEETING_DURATION
    start_time_str = minutes_to_time(start_value)
    end_time_str = minutes_to_time(end_value)
    
    # Output the day and the proposed time range in HH:MM:HH:MM format
    print(f"Monday {start_time_str}:{end_time_str}")
else:
    print("No available meeting slot found.")