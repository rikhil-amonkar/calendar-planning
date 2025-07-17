from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
solver = Solver()

# All meetings must be on Monday
solver.add(day == 1)  # Assuming Monday is represented by 1

# Meeting must be between 9:00 and 17:00
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(end_time <= 17 * 60)   # 17:00 in minutes

# Meeting duration is 30 minutes
solver.add(end_time == start_time + meeting_duration)

# Define busy times for each participant
busy_times = {
    'Andrea': [(9 * 60 + 30, 10 * 60 + 30), (13 * 60 + 30, 14 * 60 + 30)],
    'Ruth': [(12 * 60 + 30, 13 * 60), (15 * 60, 15 * 60 + 30)],
    'Steven': [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
               (13 * 60 + 30, 14 * 60), (15 * 60, 16 * 60)],
    'Grace': [],
    'Kyle': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60),
             (13 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    'Elijah': [(9 * 60, 11 * 60), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60),
               (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    'Lori': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30), (12 * 60, 13 * 60 + 30),
             (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Add constraints to avoid busy times
for person, times in busy_times.items():
    for start, end in times:
        solver.add(Or(end_time <= start, start_time >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = model[end_time].as_long()
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start // 60}:{start % 60:02}")
    print(f"End Time: {end // 60}:{end % 60:02}")
else:
    print("No solution found")