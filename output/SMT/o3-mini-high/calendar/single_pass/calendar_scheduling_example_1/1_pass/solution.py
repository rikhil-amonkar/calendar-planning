from z3 import Int, Or, Solver

# Meeting duration in minutes
duration = 30

# Define meeting start time variable (in minutes after midnight)
# Domain: must start between 9:00 (540 minutes) and 14:30 (870 minutes) 
# so that the meeting ends by 15:00.
s = Int('s')

solver = Solver()

# Domain constraint: meeting must start between 9:00 and 14:30 (ensuring end by 15:00)
solver.add(s >= 540, s <= 870)
solver.add(s + duration <= 900)  # Ensure meeting ends by 15:00

# Raymond's unavailable slots:
# - 9:00 to 9:30  -> meeting must not start before 9:30
solver.add(s >= 570)
# - 11:30 to 12:00 -> either finish by 11:30 or start at or after 12:00
solver.add(Or(s + duration <= 690, s >= 720))
# - 13:00 to 13:30 -> either finish by 13:00 or start at or after 13:30
solver.add(Or(s + duration <= 780, s >= 810))

# Billy's unavailable slots:
# - 10:00 to 10:30 -> either finish by 10:00 or start at or after 10:30
solver.add(Or(s + duration <= 600, s >= 630))
# - 12:00 to 13:00 -> either finish by 12:00 or start at or after 13:00
solver.add(Or(s + duration <= 720, s >= 780))
# Additionally, Billy prefers not to have meetings after 15:00 (enforced above)

# Donald's unavailable slots:
# - 9:00 to 9:30 -> meeting must not start before 9:30 (same as Raymond)
solver.add(s >= 570)
# - 10:00 to 11:00 -> either finish by 10:00 or start at or after 11:00
solver.add(Or(s + duration <= 600, s >= 660))
# - 12:00 to 13:00 -> either finish by 12:00 or start at or after 13:00
solver.add(Or(s + duration <= 720, s >= 780))
# - 14:00 to 14:30 -> either finish by 14:00 or start at or after 14:30
solver.add(Or(s + duration <= 840, s >= 870))

# Check if the constraints are satisfiable
if solver.check() == 'sat' or solver.check() == 1:
    model = solver.model()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration

    # Helper function to convert minutes into HH:MM 24-hour format
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    day = "Monday"
    result = (f"SOLUTION:\n"
              f"Day: {day}\n"
              f"Start Time: {minutes_to_time(meeting_start)}\n"
              f"End Time: {minutes_to_time(meeting_end)}")
    print(result)
else:
    print("No solution found.")