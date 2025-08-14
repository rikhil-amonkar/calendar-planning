from z3 import *

# Define the variables
day = Int('day')
start_time = Int('start_time')

# Define the domain for the variables
days = {'Monday': 1, 'Tuesday': 2, 'Wednesday': 3, 'Thursday': 4, 'Friday': 5}
day_values = list(days.values())
solver = Solver()

# Add constraints for the day
solver.add(day >= min(day_values))
solver.add(day <= max(day_values))

# Add constraints for the start time
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(start_time <= 16 * 60)  # 16:00 in minutes

# Nicole's constraints
nicole_busy_times = {
    2: [(16 * 60, 16 * 60 + 30)],  # Tuesday 16:00 to 16:30
    3: [(15 * 60, 15 * 60 + 30)],  # Wednesday 15:00 to 15:30
    5: [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]  # Friday 12:00 to 12:30, 15:30 to 16:00
}

# Daniel's constraints
daniel_busy_times = {
    1: [(9 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 16 * 60 + 30)],  # Monday
    2: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],  # Tuesday
    3: [(9 * 60, 10 * 60), (11 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],  # Wednesday
    4: [(11 * 60, 12 * 60), (13 * 60, 14 * 60), (15 * 60, 15 * 60 + 30)],  # Thursday
    5: [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]  # Friday
}

# Function to add constraints for busy times
def add_busy_time_constraints(busy_times):
    for d, times in busy_times.items():
        for start, end in times:
            solver.add(Or(day != d, Or(start_time >= end, start_time + 60 <= start)))

# Add constraints for Nicole and Daniel
add_busy_time_constraints(nicole_busy_times)
add_busy_time_constraints(daniel_busy_times)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = [k for k, v in days.items() if v == model[day].as_long()][0]
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + 60
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time // 60}:{meeting_start_time % 60:02}\nEnd Time: {meeting_end_time // 60}:{meeting_end_time % 60:02}")
else:
    print("No solution found")