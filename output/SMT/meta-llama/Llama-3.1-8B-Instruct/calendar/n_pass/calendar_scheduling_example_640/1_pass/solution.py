from z3 import *

def schedule_meeting(bobby_schedule, michael_schedule, meeting_duration):
    # Create Z3 solver
    solver = Solver()

    # Define variables
    day = [Bool('day_' + str(i)) for i in range(2)]
    start_time = [Int('start_time_' + str(i)) for i in range(2)]
    end_time = [Int('end_time_' + str(i)) for i in range(2)]

    # Add constraints for day
    for i in range(2):
        solver.add(day[i] == 1)  # Assume day is Monday (0) or Tuesday (1)

    # Add constraints for start time
    for i in range(2):
        solver.add(start_time[i] >= 9)  # Start time must be after 9:00
        solver.add(start_time[i] <= 17)  # Start time must be before 17:00
        solver.add(Or([start_time[i] + meeting_duration >= 17 for i in range(2)]))  # End time must be before 17:00

    # Add constraints for end time
    for i in range(2):
        solver.add(end_time[i] == start_time[i] + meeting_duration)  # End time must be equal to start time plus meeting duration

    # Add constraints for bobby's schedule
    for i in range(2):
        for j in range(len(bobby_schedule[i])):
            start = bobby_schedule[i][j][0]
            end = bobby_schedule[i][j][1]
            solver.add(Or([start_time[i] + meeting_duration > start, start_time[i] < start, end_time[i] < start]))
            solver.add(Or([start_time[i] + meeting_duration > end, start_time[i] < end, end_time[i] < end]))

    # Add constraints for michael's schedule
    for i in range(2):
        for j in range(len(michael_schedule[i])):
            start = michael_schedule[i][j][0]
            end = michael_schedule[i][j][1]
            solver.add(Or([start_time[i] + meeting_duration > start, start_time[i] < start, end_time[i] < start]))
            solver.add(Or([start_time[i] + meeting_duration > end, start_time[i] < end, end_time[i] < end]))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_to_meet = int(model.evaluate(day[0]).as_long())
        start_time_to_meet = int(model.evaluate(start_time[0]).as_long())
        end_time_to_meet = int(model.evaluate(end_time[0]).as_long())
        print(f'SOLUTION:')
        print(f'Day: {"Monday" if day_to_meet == 0 else "Tuesday"}')
        print(f'Start Time: {start_time_to_meet:02d}:00')
        print(f'End Time: {end_time_to_meet:02d}:00')
    else:
        print('No solution found')

# Existing schedules for Bobby and Michael
bobby_schedule = [[[9, 17]], [[14, 30], [15, 0]], [[9, 30], [11, 30], [12, 0], [12, 30], [13, 0], [15, 0], [15, 30], [17, 0]]]
michael_schedule = [[[9, 0], [10, 0]], [[9, 30], [10, 30], [11, 0], [11, 30], [12, 0], [14, 0], [15, 0], [16, 0], [16, 30], [17, 0]], [[9, 0], [10, 30], [11, 0], [11, 30], [12, 0], [14, 0], [15, 0], [16, 0], [16, 30], [17, 0]]]
meeting_duration = 30

schedule_meeting(bobby_schedule, michael_schedule, meeting_duration)