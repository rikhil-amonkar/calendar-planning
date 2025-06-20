from z3 import *

# Define the days and time slots
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
time_slots = ['09:00', '10:00', '11:00', '12:00', '13:00', '14:00', '15:00', '16:00']

# Define the meeting duration in hours
meeting_duration = 1

# Define the existing schedules for Carl and Margaret
carl_schedule = {
    'Monday': ['11:00', '11:30'],
    'Tuesday': ['14:30', '15:00'],
    'Wednesday': ['10:00', '11:30', '13:00', '13:30'],
    'Thursday': ['13:30', '14:00', '16:00', '16:30']
}

margaret_schedule = {
    'Monday': ['09:00', '10:30', '11:00', '17:00'],
    'Tuesday': ['09:30', '12:00', '13:30', '14:00', '15:30', '17:00'],
    'Wednesday': ['09:30', '12:00', '12:30', '13:00', '13:30', '14:30', '15:00', '17:00'],
    'Thursday': ['10:00', '12:00', '12:30', '14:00', '14:30', '17:00']
}

# Define the preferences
carl_preferences = {
    'Thursday': ['09:00', '10:00']
}

# Create the solver
s = Solver()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Int(f'start_time_{i}') for i in range(len(days))]
end_time = [Int(f'end_time_{i}') for i in range(len(days))]

# Add the constraints
for i, day_var in enumerate(day):
    s.add(day_var == True)
    s.add(start_time[i] >= 9)
    s.add(start_time[i] <= 17 - meeting_duration)
    s.add(end_time[i] == start_time[i] + meeting_duration)

    # Add constraints based on existing schedules
    for j, time_slot in enumerate(carl_schedule[days[i]]):
        s.add(Or(start_time[i] < int(time_slot[:2]) + int(time_slot[3:]), end_time[i] >= int(time_slot[:2]) + int(time_slot[3:])))
    for j, time_slot in enumerate(margaret_schedule[days[i]]):
        s.add(Or(start_time[i] < int(time_slot[:2]) + int(time_slot[3:]), end_time[i] >= int(time_slot[:2]) + int(time_slot[3:])))

    # Add constraints based on preferences
    if days[i] == 'Thursday':
        for j, time_slot in enumerate(carl_preferences[days[i]]):
            s.add(Or(start_time[i] < int(time_slot[:2]) + int(time_slot[3:]), end_time[i] >= int(time_slot[:2]) + int(time_slot[3:])))

# Solve the constraints
s.check()

# Print the solution
model = s.model()
day_index = [i for i, day_var in enumerate(day) if model[day_var] == True][0]
print(f'SOLUTION:')
print(f'Day: {days[day_index]}')
print(f'Start Time: {str(model[start_time[day_index]]).split(".")[0]}')
print(f'End Time: {str(model[end_time[day_index]])}.split(".")[0]}')