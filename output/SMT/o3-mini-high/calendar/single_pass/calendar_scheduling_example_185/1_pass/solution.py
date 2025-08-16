from z3 import Int, Solver, Or

# Meeting duration in minutes
duration = 30

# Represent the meeting’s start time (in minutes after midnight)
s = Int('s')

# Working hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Megan prefers not to have meetings before 10:00 (600 minutes), so we require s >= 600.
solver = Solver()
solver.add(s >= 600)        # must start at or after 10:00
solver.add(s + duration <= 1020)  # meeting must end by 17:00

# Define a helper function to enforce that the meeting (interval [s, s+duration))
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(busy_start, busy_end):
    return Or(s + duration <= busy_start, s >= busy_end)

# Kimberly's busy intervals (converted to minutes):
# 10:00-10:30 -> [600, 630], 11:00-12:00 -> [660, 720], 16:00-16:30 -> [960, 990]
kimberly_busy = [(600, 630), (660, 720), (960, 990)]
for interval in kimberly_busy:
    solver.add(no_overlap(interval[0], interval[1]))

# Marie's busy intervals:
# 10:00-11:00 -> [600, 660], 11:30-15:00 -> [690, 900], 16:00-16:30 -> [960, 990]
marie_busy = [(600, 660), (690, 900), (960, 990)]
for interval in marie_busy:
    solver.add(no_overlap(interval[0], interval[1]))

# Diana's busy intervals:
# 9:30-10:00 -> [570, 600], 10:30-14:30 -> [630, 870], 15:30-17:00 -> [930, 1020]
diana_busy = [(570, 600), (630, 870), (930, 1020)]
for interval in diana_busy:
    solver.add(no_overlap(interval[0], interval[1]))

# Try to solve the scheduling constraints.
if solver.check().__eq__("sat"):
    model = solver.model()
    meeting_start = model[s].as_long()  # in minutes after midnight
    meeting_end = meeting_start + duration

    # Helper function to convert minutes to HH:MM (24-hour format)
    def to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", to_time(meeting_start))
    print("End Time:", to_time(meeting_end))
else:
    print("No solution found.")