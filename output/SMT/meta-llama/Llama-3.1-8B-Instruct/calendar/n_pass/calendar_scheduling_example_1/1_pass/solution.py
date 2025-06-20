from z3 import *

# Define the day of the week
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

# Define the start and end times
start_times = [9, 10, 11, 12, 13, 14, 15, 16]
end_times = [9.5, 10.5, 11.5, 12.5, 13.5, 14.5, 15.5, 16.5]

# Define the existing schedules
schedules = {
    'Raymond': [(9, 9.5), (11.5, 12), (13, 13.5), (15, 15.5)],
    'Billy': [(10, 10.5), (12, 13), (16.5, 17)],
    'Donald': [(9, 9.5), (10, 11), (12, 13), (14, 14.5), (16, 17)]
}

# Define the preferences
preferences = {
    'Billy': [(15, 17)]
}

# Create a Z3 solver
solver = Solver()

# Define the variables
day = Int('day')
start_time = Real('start_time')
end_time = Real('end_time')

# Add the constraints
solver.add(And(
    day >= 0,
    day < len(days),
    start_time >= 9,
    start_time <= 16.5,
    end_time >= start_time,
    end_time <= 17
))

# Add the constraints for each participant
for participant, schedule in schedules.items():
    for time in schedule:
        solver.add(Or(
            And(start_time < time[0], end_time < time[0]),
            And(start_time > time[1], end_time > time[1])
        ))

# Add the preference constraints
for participant, pref in preferences.items():
    for time in pref:
        solver.add(Or(
            And(start_time < time[0], end_time < time[0]),
            And(start_time > time[1], end_time > time[1])
        ))

# Solve the constraints
solver.check()

# Get the solution
model = solver.model()

# Print the solution
print('SOLUTION:')
print(f'Day: {days[model[day].as_long()]}')
print(f'Start Time: {int(model[start_time].numerator() / model[start_time].denominator()):02d}:{int((model[start_time].numerator() % model[start_time].denominator()) / 30):02d}')
print(f'End Time: {int(model[end_time].numerator() / model[end_time].denominator()):02d}:{int((model[end_time].numerator() % model[end_time].denominator()) / 30):02d}')