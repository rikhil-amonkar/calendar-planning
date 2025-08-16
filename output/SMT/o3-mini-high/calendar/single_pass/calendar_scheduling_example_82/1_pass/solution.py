from z3 import Solver, Int, Or

def minutes_to_timestr(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# Create a Z3 solver instance
solver = Solver()

# Let 's' be the start time in minutes after midnight.
# Work day is between 09:00 (540 minutes) and 17:00 (1020 minutes).
# Since the meeting lasts 30 minutes, we require s + 30 <= 1020, i.e., s <= 990.
s = Int('s')
solver.add(s >= 540, s <= 990)

# The meeting duration is 30 minutes, giving an interval [s, s+30).

# Michael's blocked intervals:
# Meeting 1: 09:30 to 10:30  --> [570, 630)
solver.add(Or(s + 30 <= 570, s >= 630))
# Meeting 2: 15:00 to 15:30  --> [900, 930)
solver.add(Or(s + 30 <= 900, s >= 930))
# Meeting 3: 16:00 to 16:30  --> [960, 990)
solver.add(Or(s + 30 <= 960, s >= 990))

# Arthur's blocked intervals:
# Block 1: 09:00 to 12:00  --> [540, 720)
solver.add(Or(s + 30 <= 540, s >= 720))
# Block 2: 13:00 to 15:00  --> [780, 900)
solver.add(Or(s + 30 <= 780, s >= 900))
# Block 3: 15:30 to 16:00  --> [930, 960)
solver.add(Or(s + 30 <= 930, s >= 960))
# Block 4: 16:30 to 17:00  --> [990, 1020)
solver.add(Or(s + 30 <= 990, s >= 1020))

# Eric is free all day so no constraints from his schedule.

# Solve for a valid meeting start time
if solver.check() == "sat" or solver.check():
    model = solver.model()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + 30

    # Convert the meeting start and end times into HH:MM format.
    start_time_str = minutes_to_timestr(meeting_start)
    end_time_str = minutes_to_timestr(meeting_end)

    # Print the solution in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", start_time_str)
    print("End Time:", end_time_str)
else:
    print("No solution found.")