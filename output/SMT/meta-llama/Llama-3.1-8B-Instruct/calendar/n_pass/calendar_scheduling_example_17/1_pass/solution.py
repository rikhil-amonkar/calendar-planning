from z3 import *

# Define the day, start time, and end time
day = 'Monday'
start_time = 9
end_time = 17
duration = 30

# Define the participants and their schedules
schedules = {
    'Margaret': [(9, 10), (10.5, 11), (11.5, 12), (13, 13.5), (15, 15.5)],
    'Donna': [(14.5, 15), (16, 16.5)],
    'Helen': [(9, 9.5), (10, 11.5), (13, 14), (14.5, 15), (15.5, 17)]
}

# Define the preferences
preferences = {
    'Helen': (13.5, end_time)
}

# Create Z3 solver
solver = Solver()

# Define the variables
day_var = Int('day')
start_var = Int('start')
end_var = Int('end')

# Add constraints for day
solver.add(day_var == 1)  # Monday is 1

# Add constraints for start and end time
solver.add(start_var >= start_time)
solver.add(end_var <= end_time)

# Add constraints for duration
solver.add(end_var - start_var == duration)

# Add constraints for each participant's schedule
for participant, schedule in schedules.items():
    for start, end in schedule:
        solver.add(start_var + duration/60 > start)
        solver.add(end_var < end)

# Add constraints for Helen's preference
helen_preference_start, helen_preference_end = preferences['Helen']
solver.add(start_var + duration/60 > helen_preference_start)
solver.add(end_var < helen_preference_end)

# Check if there's a solution
if solver.check() == sat:
    model = solver.model()
    start_time_str = str(int(model[start_var])).zfill(2) + ':' + str(int((model[start_var] % 1) * 60)).zfill(2)
    end_time_str = str(int(model[end_var])).zfill(2) + ':' + str(int((model[end_var] % 1) * 60)).zfill(2)
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")