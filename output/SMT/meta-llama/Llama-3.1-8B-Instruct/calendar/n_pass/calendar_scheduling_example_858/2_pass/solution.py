YOUR_CODE
from z3 import *

def schedule_meeting(carl_schedules, margaret_schedules, day, duration, preference):
    # Create a Z3 solver
    solver = Solver()

    # Define variables
    day_var = [Bool(f'day_{i}') for i in range(4)]
    time_var = [Bool(f'time_{i}') for i in range(8)]
    start_time_var = [Int(f'start_time_{i}') for i in range(8)]
    end_time_var = [Int(f'end_time_{i}') for i in range(8)]

    # Add constraints for day
    for i in range(4):
        solver.add(day_var[i]!= day_var[i].not())

    solver.add(Implies(day_var[0], day == 'Monday'))
    solver.add(Implies(day_var[1], day == 'Tuesday'))
    solver.add(Implies(day_var[2], day == 'Wednesday'))
    solver.add(Implies(day_var[3], day == 'Thursday'))

    # Add constraints for time
    for i in range(8):
        solver.add(Or([time_var[i], time_var[i].not()]))
    solver.add(Implies(time_var[0], start_time_var[0] == 9))
    solver.add(Implies(time_var[0], end_time_var[0] == 10))
    solver.add(Implies(time_var[1], start_time_var[1] == 10))
    solver.add(Implies(time_var[1], end_time_var[1] == 11))
    solver.add(Implies(time_var[2], start_time_var[2] == 11))
    solver.add(Implies(time_var[2], end_time_var[2] == 12))
    solver.add(Implies(time_var[3], start_time_var[3] == 12))
    solver.add(Implies(time_var[3], end_time_var[3] == 13))
    solver.add(Implies(time_var[4], start_time_var[4] == 13))
    solver.add(Implies(time_var[4], end_time_var[4] == 14))
    solver.add(Implies(time_var[5], start_time_var[5] == 14))
    solver.add(Implies(time_var[5], end_time_var[5] == 15))
    solver.add(Implies(time_var[6], start_time_var[6] == 15))
    solver.add(Implies(time_var[6], end_time_var[6] == 16))
    solver.add(Implies(time_var[7], start_time_var[7] == 16))
    solver.add(Implies(time_var[7], end_time_var[7] == 17))

    # Add constraints for duration
    for i in range(8):
        solver.add(start_time_var[i] + duration <= end_time_var[i])

    # Add constraints for Carl's schedule
    for i in range(4):
        for j in range(8):
            if (day == 'Monday' and 9 <= start_time_var[j] <= 17 and (11 <= start_time_var[j] <= 11.5 or 11.5 <= start_time_var[j] <= 11.5)):
                solver.add(Not(day_var[i]))
            elif (day == 'Tuesday' and 9 <= start_time_var[j] <= 17 and (14.5 <= start_time_var[j] <= 15 or 14.5 <= start_time_var[j] <= 15)):
                solver.add(Not(day_var[i]))
            elif (day == 'Wednesday' and 9 <= start_time_var[j] <= 17 and (10 <= start_time_var[j] <= 11.5 or 13 <= start_time_var[j] <= 13.5)):
                solver.add(Not(day_var[i]))
            elif (day == 'Thursday' and 9 <= start_time_var[j] <= 17 and (13.5 <= start_time_var[j] <= 14 or 16 <= start_time_var[j] <= 16.5)):
                solver.add(Not(day_var[i]))

    # Add constraints for Margaret's schedule
    for i in range(4):
        for j in range(8):
            if (day == 'Monday' and 9 <= start_time_var[j] <= 17 and (9 <= start_time_var[j] <= 10.5 or 11 <= start_time_var[j] <= 17)):
                solver.add(Not(day_var[i]))
            elif (day == 'Tuesday' and 9 <= start_time_var[j] <= 17 and (9.5 <= start_time_var[j] <= 12 or 13.5 <= start_time_var[j] <= 14 or 15.5 <= start_time_var[j] <= 17)):
                solver.add(Not(day_var[i]))
            elif (day == 'Wednesday' and 9 <= start_time_var[j] <= 17 and (9.5 <= start_time_var[j] <= 12 or 12.5 <= start_time_var[j] <= 13 or 13.5 <= start_time_var[j] <= 14.5 or 15 <= start_time_var[j] <= 17)):
                solver.add(Not(day_var[i]))
            elif (day == 'Thursday' and 9 <= start_time_var[j] <= 17 and (10 <= start_time_var[j] <= 12 or 12.5 <= start_time_var[j] <= 14 or 14.5 <= start_time_var[j] <= 17)):
                solver.add(Not(day_var[i]))

    # Add preference constraint
    if preference == 'Thursday':
        for i in range(8):
            if start_time_var[i] >= 13.5 and day_var[3]:
                solver.add(Not(time_var[i]))

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        day = [str(day) for day in day_var]
        day = [day[i] for i in range(4) if model.eval(day_var[i])]
        time = [str(time) for time in time_var]
        time = [time[i] for i in range(8) if model.eval(time_var[i])]
        start_time = [str(start_time) for start_time in start_time_var]
        start_time = [start_time[i] for i in range(8) if model.eval(time_var[i])]
        end_time = [str(end_time) for end_time in end_time_var]
        end_time = [end_time[i] for i in range(8) if model.eval(time_var[i])]
        print(f'SOLUTION:')
        print(f'Day: {day[0]}')
        print(f'Start Time: {start_time[0]}')
        print(f'End Time: {end_time[0]}')
    else:
        print('NO SOLUTION')

# Define existing schedules for Carl and Margaret
carl_schedules = {
    'Monday': [(11, 11.5), (17, 17)],
    'Tuesday': [(14.5, 15), (17, 17)],
    'Wednesday': [(10, 11.5), (13, 13.5), (17, 17)],
    'Thursday': [(13.5, 14), (16, 16.5), (17, 17)]
}

margaret_schedules = {
    'Monday': [(9, 10.5), (11, 17), (17, 17)],
    'Tuesday': [(9.5, 12), (13.5, 14), (15.5, 17), (17, 17)],
    'Wednesday': [(9.5, 12), (12.5, 13), (13.5, 14.5), (15, 17), (17, 17)],
    'Thursday': [(10, 12), (12.5, 14), (14.5, 17), (17, 17)]
}

# Define the meeting duration
duration = 1

# Define the preference
preference = 'Thursday'

# Schedule the meeting
schedule_meeting(carl_schedules, margaret_schedules, 'Monday', duration, preference)