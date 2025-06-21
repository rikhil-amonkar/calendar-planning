from z3 import *

def schedule_meeting(schedules, duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    days = ['Monday']
    start_times = [9] * 24
    end_times = [9 + 1] * 24
    for i in range(1, 24):
        start_times[i] = start_times[i - 1] + 1
        end_times[i] = end_times[i - 1] + 1

    # Create a boolean array to represent the availability of each participant
    availability = [[Bool(f'{day}_{i}_{j}') for j in range(24)] for i in range(len(schedules)) for day in days]

    # Add constraints for each participant's schedule
    for i, schedule in enumerate(schedules):
        for day in days:
            for time in schedule[day]:
                for j in range(time[0], time[1]):
                    solver.assert_not(availability[i][day.index(day)][j])

    # Add constraints for the meeting duration
    for day in days:
        for start_time in range(9, 17):
            for end_time in range(start_time + 1, 17 + 1):
                if end_time - start_time >= duration:
                    for i in range(len(schedules)):
                        solver.assert(availability[i][day.index(day)][start_time] == True)
                        solver.assert(availability[i][day.index(day)][end_time - 1] == True)
                        for j in range(start_time + 1, end_time):
                            solver.assert_not(availability[i][day.index(day)][j])

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        day = days[0]
        start_time = model[day + '_0_9'].as_long()
        end_time = start_time + duration
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00'
    else:
        return 'No solution exists'

# Define the schedules
schedules = {
    'Diane': {
        'Monday': [(9*60+30, 10*60), (14*60+30, 15*60)]
    },
    'Jack': {
        'Monday': [(13*60+30, 14*60), (14*60+30, 15*60)]
    },
    'Eugene': {
        'Monday': [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 14*60+30), (15*60, 16*60+30)]
    },
    'Patricia': {
        'Monday': [(9*60+30, 10*60+30), (11*60, 12*60), (12*60+30, 14*60), (15*60, 16*60+30)]
    }
}

# Define the meeting duration
duration = 30

print(schedule_meeting(schedules, duration))