from z3 import *

# Define the days of the week as integers
MONDAY, TUESDAY, WEDNESDAY, THURSDAY = 0, 1, 2, 3

# Define the time in minutes from 9:00 to 17:00
START_TIME = 9 * 60
END_TIME = 17 * 60

# Define the meeting duration in minutes
MEETING_DURATION = 30

# Create a solver instance
solver = Solver()

# Define variables for the day and start time of the meeting
day = Int('day')
start_time = Int('start_time')

# Constraints for the day
solver.add(day >= MONDAY)
solver.add(day <= THURSDAY)

# Constraints for the start time
solver.add(start_time >= START_TIME)
solver.add(start_time + MEETING_DURATION <= END_TIME)

# Mary's busy times
mary_busy_times = [
    (TUESDAY, 10 * 60, 10 * 60 + 30),
    (TUESDAY, 15 * 60 + 30, 16 * 60),
    (WEDNESDAY, 9 * 60 + 30, 10 * 60),
    (WEDNESDAY, 15 * 60, 15 * 60 + 30),
    (THURSDAY, 9 * 60, 10 * 60),
    (THURSDAY, 10 * 60 + 30, 11 * 60 + 30)
]

# Alexis's busy times
alexis_busy_times = [
    (MONDAY, 9 * 60, 10 * 60),
    (MONDAY, 10 * 60 + 30, 12 * 60),
    (MONDAY, 12 * 60 + 30, 16 * 60 + 30),
    (TUESDAY, 9 * 60, 10 * 60),
    (TUESDAY, 10 * 60 + 30, 11 * 60 + 30),
    (TUESDAY, 12 * 60, 15 * 60 + 30),
    (TUESDAY, 16 * 60, 17 * 60),
    (WEDNESDAY, 9 * 60, 11 * 60),
    (WEDNESDAY, 11 * 60 + 30, 17 * 60),
    (THURSDAY, 10 * 60, 12 * 60),
    (THURSDAY, 14 * 60, 14 * 60 + 30),
    (THURSDAY, 15 * 60 + 30, 16 * 60),
    (THURSDAY, 16 * 60 + 30, 17 * 60)
]

# Add constraints to avoid busy times
for d, start, end in mary_busy_times:
    solver.add(Or(day != d, Or(start_time >= end, start_time + MEETING_DURATION <= start)))

for d, start, end in alexis_busy_times:
    solver.add(Or(day != d, Or(start_time >= end, start_time + MEETING_DURATION <= start)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + MEETING_DURATION

    # Convert day to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_day_str = days[meeting_day]

    # Convert time to HH:MM format
    meeting_start_time_str = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")