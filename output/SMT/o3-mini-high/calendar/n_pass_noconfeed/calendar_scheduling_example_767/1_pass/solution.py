from z3 import Solver, Int, Or

# Create the solver
solver = Solver()

# We use an integer variable for day:
# 0 = Monday, 1 = Tuesday, 2 = Wednesday
day = Int("day")
solver.add(Or(day == 0, day == 1, day == 2))

# Meeting start time "s" is defined in minutes after 9:00.
# Since work hours are 9:00 to 17:00 and the meeting lasts 60 minutes,
# the meeting must start between 0 and 420 minutes (i.e. 9:00 and 16:00).
s = Int("s")
duration = 60
solver.add(s >= 0, s <= 420)

# Helper function to express that the meeting [s, s+duration] does not overlap a blocked interval [b_start, b_end].
def no_overlap(s, duration, b_start, b_end):
    return Or(s + duration <= b_start, s >= b_end)

# Define the blocked intervals for each person, adjusted in minutes from 9:00.

# Martha's blocks:
# Monday: 16:00 to 17:00 -> [420, 480]
solver.add(Or(day != 0, no_overlap(s, duration, 420, 480)))
# Tuesday: 15:00 to 15:30 -> [360, 390]
solver.add(Or(day != 1, no_overlap(s, duration, 360, 390)))
# Wednesday: blocks 10:00 to 11:00 -> [60, 120] and 14:00 to 14:30 -> [300, 330]
solver.add(Or(day != 2, no_overlap(s, duration, 60, 120)))
solver.add(Or(day != 2, no_overlap(s, duration, 300, 330)))

# Beverly's blocks:
# Monday: 9:00 to 13:30 -> [0, 270] and 14:00 to 17:00 -> [300, 480]
solver.add(Or(day != 0, no_overlap(s, duration, 0, 270)))
solver.add(Or(day != 0, no_overlap(s, duration, 300, 480)))
# Tuesday: 9:00 to 17:00 -> [0, 480]
solver.add(Or(day != 1, no_overlap(s, duration, 0, 480)))
# Wednesday: blocks 9:30 to 15:30 -> [30, 390] and 16:30 to 17:00 -> [450, 480]
solver.add(Or(day != 2, no_overlap(s, duration, 30, 390)))
solver.add(Or(day != 2, no_overlap(s, duration, 450, 480)))

# Check if there is a solution that satisfies all constraints
if solver.check() == 'sat':
    model = solver.model()
    chosen_day = model[day].as_long()
    chosen_start = model[s].as_long()  # in minutes from 9:00

    # Convert the meeting start time back to actual clock time.
    # 9:00 is 540 minutes from midnight.
    actual_start = 9 * 60 + chosen_start
    actual_end = actual_start + duration

    start_hour = actual_start // 60
    start_min = actual_start % 60
    end_hour = actual_end // 60
    end_min = actual_end % 60

    day_names = ["Monday", "Tuesday", "Wednesday"]
    meeting_day = day_names[chosen_day]
    # Format the meeting time as "HH:MM:HH:MM"
    meeting_time = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    
    print(f"Meeting scheduled on {meeting_day} at {meeting_time}")
else:
    print("No valid meeting time could be found.")