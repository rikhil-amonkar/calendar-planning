from z3 import *

# Define the days of the week as integers
MONDAY, TUESDAY, WEDNESDAY, THURSDAY = 0, 1, 2, 3

# Define the time in minutes from 9:00 to 17:00
START_TIME = 9 * 60
END_TIME = 17 * 60

# Define the meeting duration in minutes
MEETING_DURATION = 60

# Create a solver instance
solver = Solver()

# Define variables for the meeting day and start time
meeting_day = Int('meeting_day')
meeting_start = Int('meeting_start')

# Constraints for the meeting day
solver.add(meeting_day >= MONDAY)
solver.add(meeting_day <= THURSDAY)

# Constraints for the meeting start time
solver.add(meeting_start >= START_TIME)
solver.add(meeting_start + MEETING_DURATION <= END_TIME)

# Define the busy times for Megan and Daniel
megan_busy_times = [
    (MONDAY, 13 * 60, 13 * 60 + 30),
    (MONDAY, 14 * 60, 15 * 60 + 30),
    (TUESDAY, 9 * 60, 9 * 60 + 30),
    (TUESDAY, 12 * 60, 12 * 60 + 30),
    (TUESDAY, 16 * 60, 17 * 60),
    (WEDNESDAY, 9 * 60 + 30, 10 * 60),
    (WEDNESDAY, 10 * 60 + 30, 11 * 60 + 30),
    (WEDNESDAY, 12 * 60 + 30, 14 * 60),
    (WEDNESDAY, 16 * 60, 16 * 60 + 30),
    (THURSDAY, 13 * 60 + 30, 14 * 60 + 30),
    (THURSDAY, 15 * 60, 15 * 60 + 30)
]

daniel_busy_times = [
    (MONDAY, 10 * 60, 11 * 60 + 30),
    (MONDAY, 12 * 60 + 30, 15 * 60),
    (TUESDAY, 9 * 60, 10 * 60),
    (TUESDAY, 10 * 60 + 30, 17 * 60),
    (WEDNESDAY, 9 * 60, 10 * 60),
    (WEDNESDAY, 10 * 60 + 30, 11 * 60 + 30),
    (WEDNESDAY, 12 * 60, 17 * 60),
    (THURSDAY, 9 * 60, 12 * 60),
    (THURSDAY, 12 * 60 + 30, 14 * 60 + 30),
    (THURSDAY, 15 * 60, 15 * 60 + 30),
    (THURSDAY, 16 * 60, 17 * 60)
]

# Add constraints to avoid busy times
for day, start, end in megan_busy_times:
    solver.add(Or(meeting_day != day, meeting_start + MEETING_DURATION <= start, meeting_start >= end))

for day, start, end in daniel_busy_times:
    solver.add(Or(meeting_day != day, meeting_start + MEETING_DURATION <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day = model[meeting_day].as_long()
    start = model[meeting_start].as_long()
    end = start + MEETING_DURATION

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_time = f"{start // 60:02}:{start % 60:02}"
    end_time = f"{end // 60:02}:{end % 60:02}"

    print(f"SOLUTION:\nDay: {days[day]}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")