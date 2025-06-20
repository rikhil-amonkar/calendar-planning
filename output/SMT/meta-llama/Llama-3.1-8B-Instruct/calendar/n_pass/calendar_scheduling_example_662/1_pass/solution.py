from z3 import *

def solve_meeting(gary_schedule, david_schedule, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define variables for day and time
    days = ['Monday', 'Tuesday']
    start_times = [9 * 60 + i for i in range(60)]
    end_times = [start + meeting_duration for start in start_times]

    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for day
    solver.add(day >= 0)
    solver.add(day < len(days))

    # Add constraints for start and end time
    solver.add(start_time >= 9 * 60)
    solver.add(start_time < 17 * 60)
    solver.add(end_time >= 9 * 60)
    solver.add(end_time < 17 * 60)
    solver.add(start_time < end_time)

    # Add constraints for meeting duration
    solver.add(end_time - start_time == meeting_duration)

    # Add constraints for gary's schedule
    for time in gary_schedule['Monday']:
        solver.add(Or(start_time + If(day == 0, 0, 24 * 60) + i < time for i in range(60)))
    for time in gary_schedule['Tuesday']:
        solver.add(Or(start_time + If(day == 1, 0, 24 * 60) + i < time for i in range(60)))

    # Add constraints for david's schedule
    for time in david_schedule['Monday']:
        solver.add(Or(start_time + If(day == 0, 0, 24 * 60) + i < time for i in range(60)))
    for time in david_schedule['Tuesday']:
        solver.add(Or(start_time + If(day == 1, 0, 24 * 60) + i < time for i in range(60)))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_val = days[model[day].as_long()]
        start_time_val = model[start_time].as_long() // 60
        end_time_val = model[end_time].as_long() // 60
        print(f'SOLUTION:')
        print(f'Day: {day_val}')
        print(f'Start Time: {start_time_val:02d}:00')
        print(f'End Time: {end_time_val:02d}:00')
    else:
        print('No solution found.')

# Define existing schedules
gary_schedule = {
    'Monday': [9 * 60 + 30, 11 * 60, 14 * 60 + 30, 16 * 60 + 30],
    'Tuesday': [9 * 60, 10 * 60 + 30, 14 * 60 + 30, 16 * 60]
}
david_schedule = {
    'Monday': [9 * 60, 10 * 60, 14 * 60 + 30, 16 * 60 + 30],
    'Tuesday': [9 * 60, 10 * 60, 11 * 60, 13 * 60, 14 * 60 + 30, 15 * 60, 16 * 60, 16 * 60 + 30]
}

# Solve the problem
solve_meeting(gary_schedule, david_schedule, 60)