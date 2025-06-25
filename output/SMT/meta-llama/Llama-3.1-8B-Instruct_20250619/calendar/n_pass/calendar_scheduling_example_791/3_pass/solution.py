from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the hours of the day
hours = range(9, 18)

# Define the meeting duration
meeting_duration = 0.5

# Define the existing schedules for Nicole and Ruth
nicole_schedule = {
    'Monday': [(9, 9.5), (13, 13.5), (14.5, 15.5)],
    'Tuesday': [(9, 9.5), (11.5, 13.5), (14.5, 15.5)],
    'Wednesday': [(10, 11), (12.5, 15), (16, 17)]
}

ruth_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9.5, 10.5), (11, 11.5), (12, 12.5), (13.5, 15.5), (16, 16.5)]
}

# Define Ruth's preference
ruth_preference = {
    'Wednesday': [(13.5, 17)]
}

# Define the solver
solver = Optimize()

# Define the variables
day = [Bool(f'day_{i}') for i in range(len(days))]
start_time = [Real(f'start_time_{i}') for i in range(len(days))]
end_time = [Real(f'end_time_{i}') for i in range(len(days))]

# Define the constraints
for i in range(len(days)):
    solver.add(day[i] == False)  # Initialize day[i] to False

for i in range(len(days)):
    for j in range(9, 17):
        for k in range(9, 17):
            if k - j == int(meeting_duration * 60):
                # Check if the meeting time conflicts with Nicole's schedule
                conflict_nicole = False
                if days[i] in nicole_schedule:
                    for conflict in nicole_schedule[days[i]]:
                        if (j, k) == conflict:
                            conflict_nicole = True
                            break
                # Check if the meeting time conflicts with Ruth's schedule
                conflict_ruth = False
                if days[i] in ruth_schedule:
                    for conflict in ruth_schedule[days[i]]:
                        if (j, k) == conflict:
                            conflict_ruth = True
                            break
                # Check if the meeting time conflicts with Ruth's preference
                conflict_ruth_preference = False
                if days[i] in ruth_preference:
                    for conflict in ruth_preference[days[i]]:
                        if (j, k) == conflict:
                            conflict_ruth_preference = True
                            break
                # Check if the meeting time conflicts with Ruth's schedule on Wednesday after 13:30
                conflict_ruth_wednesday = False
                if days[i] == 'Wednesday' and 13.5 <= j <= 17 and 13.5 <= k <= 17:
                    conflict_ruth_wednesday = True
                # If the meeting time does not conflict with anyone's schedule, add it to the solver
                if not conflict_nicole and not conflict_ruth and not conflict_ruth_preference and not conflict_ruth_wednesday:
                    solver.add(day[i] == True)
                    solver.add(start_time[i] == j)
                    solver.add(end_time[i] == k)

# Solve the optimization problem
solution = solver.check()

if solution == sat:
    model = solver.model()
    day_idx = [day[i].as_bool() for i in range(len(days))].index(True)
    print(f'SOLUTION:')
    print(f'Day: {days[day_idx]}')
    print(f'Start Time: {model.evaluate(start_time[day_idx]).as_real().as_decimal().limit_denominator()}')
    print(f'End Time: {model.evaluate(end_time[day_idx]).as_real().as_decimal().limit_denominator()}')
else:
    print('No solution found')