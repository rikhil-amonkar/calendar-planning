from z3 import *

def solve_meeting_schedule():
    # Define the variables
    day = [Bool('day_mon') + Bool('day_tue') + Bool('day_wed') for _ in range(3)]
    start_time = [Int('start_mon') + Int('start_tue') + Int('start_wed') for _ in range(3)]
    end_time = [Int('end_mon') + Int('end_tue') + Int('end_wed') for _ in range(3)]

    # Define the constraints
    amy_busy = [
        (day[0] + start_time[0] >= 9 + 0*30) + (day[0] + start_time[0] <= 17 + 0*30),
        (day[0] + start_time[0] >= 11 + 0*30) + (day[0] + start_time[0] < 11 + 0*30 + 30),
        (day[0] + start_time[0] >= 13 + 30*30) + (day[0] + start_time[0] < 14 + 30*30)
    ]
    pamela_busy = [
        (day[0] + start_time[0] >= 9 + 0*30) + (day[0] + start_time[0] < 10 + 0*30 + 30),
        (day[0] + start_time[0] >= 11 + 0*30) + (day[0] + start_time[0] < 16 + 30*30),
        (day[1] + start_time[1] >= 9 + 0*30) + (day[1] + start_time[1] < 9 + 0*30 + 30),
        (day[1] + start_time[1] >= 10 + 0*30) + (day[1] + start_time[1] < 17 + 0*30),
        (day[2] + start_time[2] >= 9 + 0*30) + (day[2] + start_time[2] < 9 + 0*30 + 30),
        (day[2] + start_time[2] >= 10 + 0*30) + (day[2] + start_time[2] < 11 + 0*30),
        (day[2] + start_time[2] >= 11 + 30*30) + (day[2] + start_time[2] < 13 + 30*30),
        (day[2] + start_time[2] >= 14 + 30*30) + (day[2] + start_time[2] < 15 + 30*30),
        (day[2] + start_time[2] >= 16 + 0*30) + (day[2] + start_time[2] < 16 + 0*30 + 30)
    ]
    pamela_preference = [
        (day[0] + start_time[0] >= 10 + 0*30) + (day[0] + start_time[0] < 17 + 0*30),
        (day[1] + start_time[1] >= 10 + 0*30) + (day[1] + start_time[1] < 17 + 0*30),
        (day[2] + start_time[2] >= 16 + 0*30) + (day[2] + start_time[2] < 17 + 0*30)
    ]
    meeting_duration = [
        (day[0] + end_time[0] - day[0] - start_time[0] == 30),
        (day[1] + end_time[1] - day[1] - start_time[1] == 30),
        (day[2] + end_time[2] - day[2] - start_time[2] == 30)
    ]

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    for constraint in amy_busy + pamela_busy + pamela_preference + meeting_duration:
        solver.add(constraint)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_to_meet = model[day[0]] + model[day[1]] + model[day[2]]
        start_time_to_meet = model[start_time[0]] + model[start_time[1]] + model[start_time[2]]
        end_time_to_meet = model[end_time[0]] + model[end_time[1]] + model[end_time[2]]

        # Print the solution
        if day_to_meet == 1:
            day_to_meet_str = 'Monday'
        elif day_to_meet == 2:
            day_to_meet_str = 'Tuesday'
        else:
            day_to_meet_str = 'Wednesday'
        print(f'SOLUTION:')
        print(f'Day: {day_to_meet_str}')
        print(f'Start Time: {int(start_time_to_meet/30):02d}:{int(start_time_to_meet%30):02d}')
        print(f'End Time: {int(end_time_to_meet/30):02d}:{int(end_time_to_meet%30):02d}')
    else:
        print('No solution found')

solve_meeting_schedule()