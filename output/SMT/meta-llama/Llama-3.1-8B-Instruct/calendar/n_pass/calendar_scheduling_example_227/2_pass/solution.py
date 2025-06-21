from z3 import *

def schedule_meeting():
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = Int('end_time')
    duration = 30  # Meeting duration in minutes
    start_time_bounds = [9 * 60, 17 * 60]  # 9:00 to 17:00 in minutes

    # Define the constraints
    constraints = [
        And(start_time >= start_time_bounds[0], start_time <= start_time_bounds[1]),  # Start time within work hours
        start_time + duration <= 17 * 60,  # End time within work hours
        Or(start_time >= 14 * 60, start_time <= 11 * 60 + 30),  # David does not want to meet before 14:00
    ]

    # Define the existing schedules
    natalie_schedule = [0, 24 * 60]  # Natalie's schedule is wide open the entire day
    david_schedule = [11 * 60, 11 * 60 + 30], [14 * 60, 14 * 60 + 30]  # David's schedule
    douglas_schedule = [9 * 60 + 30, 10 * 60], [11 * 60, 11 * 60 + 30], [13 * 60, 13 * 60 + 30], [14 * 60, 14 * 60 + 30]  # Douglas' schedule
    ralph_schedule = [9 * 60, 9 * 60 + 30], [10 * 60, 11 * 60], [11 * 60 + 30, 12 * 60 + 30], [13 * 60 + 30, 15 * 60], [15 * 60 + 30, 16 * 60], [16 * 60 + 30, 17 * 60]  # Ralph's schedule
    jordan_schedule = [9 * 60, 10 * 60], [12 * 60, 12 * 60 + 30], [13 * 60, 13 * 60 + 30], [14 * 60, 14 * 60 + 30], [15 * 60 + 30, 17 * 60]  # Jordan's schedule

    # Add constraints for each participant's schedule
    for schedule in [natalie_schedule, david_schedule, douglas_schedule, ralph_schedule, jordan_schedule]:
        for i in range(len(schedule)):
            start = schedule[i]
            if i + 1 < len(schedule):
                end = schedule[i + 1]
                constraints.append(Or(start > end_time + duration, start > start_time, end_time > end))
            else:
                constraints.append(start > end_time + duration)

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    solver.add(start_time + duration == end_time)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        hours_start = start_time_value // 60
        minutes_start = start_time_value % 60
        hours_end = end_time_value // 60
        minutes_end = end_time_value % 60
        return f'SOLUTION:\nDay: {day}\nStart Time: {hours_start:02d}:{minutes_start:02d}\nEnd Time: {hours_end:02d}:{minutes_end:02d}'
    else:
        return 'No solution found'

print(schedule_meeting())