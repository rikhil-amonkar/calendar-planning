from z3 import *

# Define the time slots as integers from 0 to 47 (9:00 to 16:30 in 30-minute increments)
def time_to_int(hour, minute):
    return (hour - 9) * 2 + (minute // 30)

def int_to_time(t):
    hour = t // 2 + 9
    minute = (t % 2) * 30
    return f"{hour:02}:{minute:02}"

# Create a solver instance
solver = Solver()

# Define the meeting time variable
meeting_start = Int('meeting_start')

# Define the constraints
# Meeting must be between 9:00 and 16:30 (inclusive)
solver.add(meeting_start >= time_to_int(9, 0))
solver.add(meeting_start <= time_to_int(16, 30) - 1)  # 16:30 is not included

# Meeting duration is 30 minutes
meeting_end = meeting_start + 1

# David's constraints: busy from 11:30 to 12:00, 14:30 to 15:00; prefers after 14:00
david_busy = Or(
    And(meeting_start >= time_to_int(11, 30), meeting_start <= time_to_int(11, 59)),
    And(meeting_start >= time_to_int(14, 30), meeting_start <= time_to_int(14, 59))
)
solver.add(Not(david_busy))
solver.add(meeting_start >= time_to_int(14, 0))

# Douglas's constraints: busy from 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00
douglas_busy = Or(
    And(meeting_start >= time_to_int(9, 30), meeting_start <= time_to_int(9, 59)),
    And(meeting_start >= time_to_int(11, 30), meeting_start <= time_to_int(11, 59)),
    And(meeting_start >= time_to_int(13, 0), meeting_start <= time_to_int(13, 29)),
    And(meeting_start >= time_to_int(14, 30), meeting_start <= time_to_int(14, 59))
)
solver.add(Not(douglas_busy))

# Ralph's constraints: busy from 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00
ralph_busy = Or(
    And(meeting_start >= time_to_int(9, 0), meeting_start <= time_to_int(9, 29)),
    And(meeting_start >= time_to_int(10, 0), meeting_start <= time_to_int(10, 59)),
    And(meeting_start >= time_to_int(11, 30), meeting_start <= time_to_int(12, 29)),
    And(meeting_start >= time_to_int(13, 30), meeting_start <= time_to_int(14, 59)),
    And(meeting_start >= time_to_int(15, 30), meeting_start <= time_to_int(15, 59))
)
solver.add(Not(ralph_busy))

# Jordan's constraints: busy from 9:00 to 10:00, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 15:30 to 17:00
jordan_busy = Or(
    And(meeting_start >= time_to_int(9, 0), meeting_start <= time_to_int(9, 59)),
    And(meeting_start >= time_to_int(12, 0), meeting_start <= time_to_int(12, 29)),
    And(meeting_start >= time_to_int(13, 0), meeting_start <= time_to_int(13, 29)),
    And(meeting_start >= time_to_int(14, 30), meeting_start <= time_to_int(14, 59)),
    And(meeting_start >= time_to_int(15, 30), meeting_start <= time_to_int(15, 59))
)
solver.add(Not(jordan_busy))

# Additional constraint to avoid the time slot from 15:30 to 17:00
solver.add(meeting_start < time_to_int(15, 30))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = meeting_start_time + 1
    print(f"SOLUTION:\nDay: Monday\nStart Time: {int_to_time(meeting_start_time)}\nEnd Time: {int_to_time(meeting_end_time)}")
else:
    print("No solution found.")