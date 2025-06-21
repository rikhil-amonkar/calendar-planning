YOUR_CODE
from z3 import *

def schedule_meeting(terry_schedule, frances_schedule, meeting_duration, day_preferences=None, frances_avoid_tuesday=False):
    # Create Z3 variables for the meeting day, start time, and end time
    day = [Bool(f'day_{i}') for i in range(5)]
    start_time = [Int(f'start_time_{i}') for i in range(5)]
    end_time = [Int(f'end_time_{i}') for i in range(5)]

    # Define the constraints for the meeting day
    if day_preferences is not None:
        for i, preferred_day in enumerate(day_preferences):
            day[i].eq(preferred_day)
    elif frances_avoid_tuesday:
        day[1].eq(False)

    # Define the constraints for the start and end times
    for i in range(5):
        for j in range(1440):  # Iterate over all possible start times
            start_time[i].eq(j)
            end_time[i].eq(j + meeting_duration)
            for terry_time in terry_schedule[i]:
                terry_time_start, terry_time_end = terry_time
                if And(start_time[i] >= terry_time_start, start_time[i] < terry_time_end):
                    start_time[i].eq(False)  # Ensure the meeting does not conflict with Terry's schedule
            for frances_time in frances_schedule[i]:
                frances_time_start, frances_time_end = frances_time
                if And(start_time[i] >= frances_time_start, start_time[i] < frances_time_end):
                    start_time[i].eq(False)  # Ensure the meeting does not conflict with Frances's schedule

    # Find a solution that satisfies all the constraints
    solver = Solver()
    for i in range(5):
        solver.add(day[i])
        solver.add(start_time[i] >= 0)
        solver.add(start_time[i] <= 720)
        solver.add(end_time[i] >= 0)
        solver.add(end_time[i] <= 720)
    solver.add(Or([day[i] for i in range(5)]))  # Ensure at least one day is selected
    solver.add(Or([start_time[i]!= 0 for i in range(5)]))  # Ensure at least one start time is selected
    solution = solver.check()
    if solution == sat:
        model = solver.model()
        day_index = [i for i, val in enumerate(model[day[0]]) if val == True][0]
        start_time_index = [i for i, val in enumerate(model[start_time[day_index]]) if val!= 0][0]
        end_time_index = [i for i, val in enumerate(model[end_time[day_index]]) if val!= 0][0]
        start_time_value = model[start_time[day_index]].as_long() // 60  # Convert minutes to hours
        end_time_value = (model[end_time[day_index]].as_long() // 60) + meeting_duration  # Convert minutes to hours
        return f'SOLUTION:\nDay: {["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][day_index]}\nStart Time: {start_time_value:02d}:00\nEnd Time: {end_time_value:02d}:00'
    else:
        return 'No solution found'

terry_schedule = [
    [(30 * 60, 60 * 60), (2.5 * 60 * 60, 4 * 60 * 60), (15 * 60, 17 * 60)],
    [(9.5 * 60, 10 * 60), (10.5 * 60, 11 * 60), (14 * 60, 14.5 * 60), (16 * 60, 16.5 * 60)],
    [(9.5 * 60, 10 * 60), (11 * 60, 12 * 60), (13 * 60, 13.5 * 60), (15 * 60, 16 * 60), (16.5 * 60, 17 * 60)],
    [(9.5 * 60, 10 * 60), (12 * 60, 12.5 * 60), (13 * 60, 14.5 * 60), (16 * 60, 16.5 * 60)],
    [(9 * 60, 11.5 * 60), (12 * 60, 12.5 * 60), (13.5 * 60, 16 * 60), (16.5 * 60, 17 * 60)]
]

frances_schedule = [
    [(9.5 * 60, 11 * 60), (11.5 * 60, 13 * 60), (14 * 60, 14.5 * 60), (15 * 60, 16 * 60)],
    [(9 * 60, 9.5 * 60), (10 * 60, 10.5 * 60), (11 * 60, 12 * 60), (13 * 60, 14.5 * 60), (15.5 * 60, 16.5 * 60)],
    [(9.5 * 60, 10 * 60), (11 * 60, 12 * 60), (11.5 * 60, 16 * 60), (16.5 * 60, 17 * 60)],
    [(11 * 60, 12.5 * 60), (14.5 * 60, 17 * 60)],
    [(9.5 * 60, 10.5 * 60), (11 * 60, 12.5 * 60), (13 * 60, 16 * 60), (16.5 * 60, 17 * 60)]
]

print(schedule_meeting(terry_schedule, frances_schedule, 30 * 60))