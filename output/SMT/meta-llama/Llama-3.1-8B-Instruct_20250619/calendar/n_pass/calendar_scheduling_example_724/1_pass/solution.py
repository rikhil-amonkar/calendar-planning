from z3 import *

def schedule_meeting(available_days, tyler_schedule, ruth_schedule, tyler_preference):
    # Create Z3 solver
    solver = Solver()

    # Define variables for day, start time, and end time
    day = [Bool(f'day_{i}') for i in range(len(available_days))]
    start_time = [Int(f'start_time_{i}') for i in range(len(available_days))]
    end_time = [Int(f'end_time_{i}') for i in range(len(available_days))]

    # Add constraints for day
    for i, d in enumerate(available_days):
        solver.add(day[i] == d)

    # Add constraints for start and end time
    for i in range(len(available_days)):
        solver.add(start_time[i] >= 9)
        solver.add(start_time[i] <= 17)
        solver.add(end_time[i] >= 9)
        solver.add(end_time[i] <= 17)
        solver.add(end_time[i] - start_time[i] == 30)  # Meeting duration is 30 minutes

    # Add constraints for Tyler's schedule
    for i, (s, e) in enumerate(tyler_schedule):
        for j in range(len(available_days)):
            solver.add(Or(start_time[j] < s, start_time[j] > e))
            solver.add(Or(end_time[j] < s, end_time[j] > e))

    # Add constraints for Ruth's schedule
    for i, (s, e) in enumerate(ruth_schedule):
        for j in range(len(available_days)):
            solver.add(Or(start_time[j] < s, start_time[j] > e))
            solver.add(Or(end_time[j] < s, end_time[j] > e))

    # Add constraints for Tyler's preference
    for i in range(len(available_days)):
        if available_days[i] == 'Monday' and start_time[i] < 16:
            solver.add(False)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_index = 0
        for i in range(len(available_days)):
            if model[day[i]]:
                day_index = i
                break

        # Print the solution
        print(f'SOLUTION:')
        print(f'Day: {available_days[day_index]}')
        print(f'Start Time: {model[start_time[day_index]].as_long():02d}:{model[start_time[day_index]].as_long() % 60:02d}')
        print(f'End Time: {(model[start_time[day_index]].as_long() + 30) % 24:02d}:{(model[start_time[day_index]].as_long() + 30) % 60:02d}')
    else:
        print('No solution found.')

# Define the problem
available_days = ['Monday', 'Tuesday', 'Wednesday']
tyler_schedule = [(9, 9.5), (14.5, 15), (10.5, 11), (12.5, 13), (13.5, 14), (16.5, 17)]
ruth_schedule = [(9, 10), (10.5, 12), (12.5, 14.5), (15, 16), (16.5, 17), (9, 17), (9, 17)]
tyler_preference = True

schedule_meeting(available_days, tyler_schedule, ruth_schedule, tyler_preference)