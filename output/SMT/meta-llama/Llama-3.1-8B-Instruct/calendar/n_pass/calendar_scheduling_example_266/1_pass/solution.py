from z3 import *

def schedule_meeting(schedules, duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the day
    day = 0  # Since the problem only considers one day (Monday)

    # Define the start time
    start_time = [0] * len(schedules)
    for i in range(len(schedules)):
        start_time[i] = Int(f'start_time_{i}')

    # Define the end time
    end_time = [0] * len(schedules)
    for i in range(len(schedules)):
        end_time[i] = start_time[i] + duration

    # Define the constraints
    for i in range(len(schedules)):
        for j in range(len(schedules[i])):
            if schedules[i][j][0] <= start_time[i] + duration <= schedules[i][j][1]:
                solver.assert_and_track(start_time[i] + duration <= schedules[i][j][0], f'conflict_{i}_{j}')

    for i in range(len(schedules)):
        solver.assert_and_track(start_time[i] >= 9 * 60, f'start_time_{i}_lower_bound')
        solver.assert_and_track(start_time[i] <= 17 * 60, f'start_time_{i}_upper_bound')

    # Define the meeting duration constraint
    for i in range(len(schedules)):
        solver.assert_and_track(end_time[i] - start_time[i] == duration, f'duration_{i}')

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        for i in range(len(schedules)):
            start_time_i = model[start_time[i]].as_long() // 60
            end_time_i = model[end_time[i]].as_long() // 60
            return f'SOLUTION:\nDay: Monday\nStart Time: {start_time_i:02d}:00\nEnd Time: {end_time_i:02d}:00'
    else:
        return 'No solution found'

# Define the schedules and duration
schedules = [
    [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60)],
    [(11 * 60 + 30, 12 * 60), (15 * 60, 15 * 60 + 30)],
    [(9 * 60, 9 * 60 + 30), (13 * 60, 13 * 60 + 30)],
    [(9 * 60, 11 * 60), (11 * 60 + 30, 16 * 60 + 30)],
    [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
]
duration = 30

# Print the solution
print(schedule_meeting(schedules, duration))