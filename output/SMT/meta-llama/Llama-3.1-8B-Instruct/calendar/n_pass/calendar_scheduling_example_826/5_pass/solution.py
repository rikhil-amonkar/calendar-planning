from z3 import *

def schedule_meeting(cheryl_schedule, james_schedule, day, duration):
    # Create Z3 variables
    start_time = [Bool(f'start_time_{day}_{i}') for i in range(len(james_schedule[day]))]
    
    # Create Z3 constraints
    constraints = []
    for i in range(len(james_schedule[day])):
        constraints.append(Implies(start_time[i], james_schedule[day][i][0] < start_time[i] + duration))
        constraints.append(Implies(start_time[i], start_time[i] + duration <= james_schedule[day][i][1]))
    
    # Ensure the meeting doesn't conflict with Cheryl's schedule
    for i in range(len(james_schedule[day])):
        for j in range(len(cheryl_schedule[day])):
            constraints.append(Implies(start_time[i], Not(cheryl_schedule[day][j][0] < start_time[i] + duration and start_time[i] + duration <= cheryl_schedule[day][j][1])))
    
    # Ensure the meeting doesn't conflict with Cheryl's preferences
    if day == 'Wednesday' or day == 'Thursday':
        constraints.append(Not(Or(*[start_time[i] for i in range(len(james_schedule[day]))])))
    
    # Find a valid solution
    solver = Solver()
    solver.add(constraints)
    solver.add(Or(*start_time))
    if solver.check() == sat:
        model = solver.model()
        start_index = [i for i, x in enumerate(model.evaluate(start_time).as_bool()) if x == True][0]
        return f'Day: {day}\nStart Time: {james_schedule[day][start_index][0]:02d}:{james_schedule[day][start_index][1]:02d}\nEnd Time: {(james_schedule[day][start_index][0] + duration):02d}:{(james_schedule[day][start_index][1] + duration):02d}'
    else:
        return 'No solution found'

# Define Cheryl's and James' schedules
cheryl_schedule = {
    'Monday': [(9, 0), (11, 0), (12, 0), (16, 0)],
    'Tuesday': [(9, 0), (11, 0), (12, 0), (16, 0)],
    'Wednesday': [(9, 0), (11, 30), (12, 30), (16, 0)],
    'Thursday': [(9, 30), (12, 0), (13, 0), (14, 0), (16, 30)]
}

james_schedule = {
    'Monday': [(9, 30), (10, 30), (12, 30), (14, 30), (16, 30)],
    'Tuesday': [(9, 0), (11, 30), (12, 30), (16, 0)],
    'Wednesday': [(10, 0), (12, 0), (13, 30)],
    'Thursday': [(9, 30), (12, 0), (13, 0), (14, 0), (16, 30)]
}

# Find the earliest available time
solutions = []
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday']:
    if james_schedule[day]:
        solution = schedule_meeting(cheryl_schedule, james_schedule, day, 30)
        if solution!= 'No solution found':
            solutions.append(solution)

# Print the solution
if solutions:
    print('SOLUTION:')
    for solution in solutions:
        print(solution)
else:
    print('No solution found')