from z3 import *

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a Z3 solver instance
solver = Solver()

# Define variables for the day and time slot
day_var = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints for the day
solver.add(day_var >= 0)
solver.add(day_var < len(days))

# Define the constraints for the time slot
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(Or(start_minute == 0, start_minute == 30))

# Define the meeting duration (1 hour)
meeting_duration = 60  # in minutes

# Define the constraints for Nicole's schedule
nicole_busy = [
    ("Tuesday", 16, 16, 30),
    ("Wednesday", 15, 15, 30),
    ("Friday", 12, 12, 30),
    ("Friday", 15, 16, 0)
]

# Define the constraints for Daniel's schedule
daniel_busy = [
    ("Monday", 9, 12, 30),
    ("Monday", 13, 13, 30),
    ("Monday", 14, 16, 30),
    ("Tuesday", 9, 10, 30),
    ("Tuesday", 11, 12, 30),
    ("Tuesday", 13, 13, 30),
    ("Tuesday", 15, 16, 0),
    ("Tuesday", 16, 17, 0),
    ("Wednesday", 9, 10, 0),
    ("Wednesday", 11, 12, 30),
    ("Wednesday", 13, 13, 30),
    ("Wednesday", 14, 14, 30),
    ("Wednesday", 16, 17, 0),
    ("Thursday", 11, 12, 0),
    ("Thursday", 13, 14, 0),
    ("Thursday", 15, 15, 30),
    ("Friday", 10, 11, 0),
    ("Friday", 11, 12, 0),
    ("Friday", 12, 14, 30),
    ("Friday", 15, 15, 30),
    ("Friday", 16, 16, 30)
]

# Function to convert time to minutes since 9:00
def time_to_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Add constraints to avoid Nicole's busy times
for day, h, m, m_end in nicole_busy:
    day_index = days.index(day)
    start = time_to_minutes(h, m)
    end = time_to_minutes(h + (m_end + 59) // 60, (m_end + 59) % 60)
    solver.add(Or(day_var != day_index, start_hour * 60 + start_minute + meeting_duration <= start, start_hour * 60 + start_minute >= end))

# Add constraints to avoid Daniel's busy times
for day, h, m, m_end in daniel_busy:
    day_index = days.index(day)
    start = time_to_minutes(h, m)
    end = time_to_minutes(h + (m_end + 59) // 60, (m_end + 59) % 60)
    solver.add(Or(day_var != day_index, start_hour * 60 + start_minute + meeting_duration <= start, start_hour * 60 + start_minute >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_index = model[day_var].as_long()
    start_time_minutes = model[start_hour].as_long() * 60 + model[start_minute].as_long()
    start_hour = start_time_minutes // 60 + 9
    start_minute = start_time_minutes % 60
    end_hour = start_hour + meeting_duration // 60
    end_minute = start_minute + meeting_duration % 60
    if end_minute >= 60:
        end_hour += 1
        end_minute -= 60
    print(f"SOLUTION:\nDay: {days[day_index]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")