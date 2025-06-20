YOUR_CODE
from z3 import *

def schedule_meeting():
    # Define the day
    day = "Monday"

    # Define the start and end time of work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the meeting duration
    meeting_duration = 30

    # Define the existing schedules for each participant
    doris_schedule = [9 * 60, 11 * 60, 13 * 60 + 30, 16 * 60]
    theresa_schedule = [10 * 60, 12 * 60]
    christian_schedule = []
    terry_schedule = [9 * 60 + 30, 10 * 60, 11 * 60 + 30, 12 * 60, 13 * 60, 14 * 60 + 30, 15 * 60 + 30, 16 * 60]
    carolyn_schedule = [9 * 60, 10 * 60 + 30, 11 * 60, 12 * 60, 13 * 60 + 30, 14 * 60 + 30, 15 * 60]
    kyle_schedule = [9 * 60, 9 * 60 + 30, 11 * 60 + 30, 12 * 60, 13 * 60, 14 * 60 + 30, 16 * 60]

    # Create a Z3 solver
    solver = Solver()

    # Define the variables for the start time of the meeting
    start_time_var = [Bool(f'start_time_{i}') for i in range(7)]

    # Add constraints for each participant's schedule
    for i in range(7):
        constraint = []
        for j in range(len(doris_schedule) - 1):
            constraint.append((start_time + i * 30) >= doris_schedule[j] and (start_time + i * 30 + meeting_duration) <= doris_schedule[j + 1])
        for j in range(len(theresa_schedule) - 1):
            constraint.append((start_time + i * 30) >= theresa_schedule[j] and (start_time + i * 30 + meeting_duration) <= theresa_schedule[j + 1])
        for j in range(len(terry_schedule) - 1):
            constraint.append((start_time + i * 30) >= terry_schedule[j] and (start_time + i * 30 + meeting_duration) <= terry_schedule[j + 1])
        for j in range(len(carolyn_schedule) - 1):
            constraint.append((start_time + i * 30) >= carolyn_schedule[j] and (start_time + i * 30 + meeting_duration) <= carolyn_schedule[j + 1])
        for j in range(len(kyle_schedule) - 1):
            constraint.append((start_time + i * 30) >= kyle_schedule[j] and (start_time + i * 30 + meeting_duration) <= kyle_schedule[j + 1])
        solver.add(Or([start_time_var[i] == False] + constraint))

    # Add constraints for the start and end time of the meeting
    for i in range(6):
        solver.add(Implies(start_time_var[i], start_time_var[i + 1]))
    solver.add(And([start_time_var[0], (start_time + 30 * 6) <= end_time]))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time_var[0]].as_long() // 60
        end_time_value = (model[start_time_var[0]].as_long() // 60 + meeting_duration) % 24
        print(f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value:02d}:{(start_time_value * 60) % 60:02d}\nEnd Time: {end_time_value:02d}:{(end_time_value * 60) % 60:02d}')
    else:
        print('No solution found')

schedule_meeting()