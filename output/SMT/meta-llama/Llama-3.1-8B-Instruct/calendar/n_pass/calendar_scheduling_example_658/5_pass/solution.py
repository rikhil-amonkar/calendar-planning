from z3 import *

def schedule_meeting(shirley_schedule, albert_schedule, meeting_duration, day, preference):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    day_var = Int('day')
    shirley_start_var = Int('shirley_start')
    albert_start_var = Int('albert_start')
    end_time_var = Int('end_time')

    # Define the constraints
    solver.add(day_var == day)
    solver.add(shirley_start_var >= 9 * 60)
    solver.add(shirley_start_var <= 17 * 60)
    solver.add(albert_start_var >= 9 * 60)
    solver.add(albert_start_var <= 17 * 60)
    solver.add(shirley_start_var + meeting_duration <= 17 * 60)
    solver.add(albert_start_var + meeting_duration <= 17 * 60)

    # Add constraints based on the schedules
    for shirley_time in shirley_schedule:
        if shirley_time[0] == day:
            solver.add(shirley_start_var!= shirley_time[0] * 60 + shirley_time[1])
    for albert_time in albert_schedule:
        if albert_time[0] == day:
            solver.add(albert_start_var!= albert_time[0] * 60 + albert_time[1])

    # Add constraints based on the preference
    if preference:
        for shirley_time in shirley_schedule:
            if shirley_time[0] == 1 and shirley_time[1] >= 30:
                solver.add(shirley_start_var!= shirley_time[0] * 60 + shirley_time[1])

    # Add constraints to ensure the meeting duration
    solver.add(end_time_var == shirley_start_var + meeting_duration)

    # Add constraints to ensure the meeting time is within the work hours
    solver.add(shirley_start_var >= 9 * 60)
    solver.add(shirley_start_var + meeting_duration <= 17 * 60)

    # Check if there is a solution
    if solver.check() == sat:
        model = solver.model()
        day_to_meet = model[day_var].as_long()
        start_hour = model[shirley_start_var].as_long() // 60
        start_minute = model[shirley_start_var].as_long() % 60
        end_hour = (model[shirley_start_var].as_long() + meeting_duration) // 60
        end_minute = (model[shirley_start_var].as_long() + meeting_duration) % 60
        return f'Day: {day_to_meet}, Start Time: {start_hour:02d}:{start_minute:02d}, End Time: {end_hour:02d}:{end_minute:02d}'
    else:
        return 'No solution found'

# Example usage
shirley_schedule = [(1, 30), (1, 60), (1, 120), (2, 30)]
albert_schedule = [(1, 0), (1, 120), (1, 150), (2, 30), (2, 90), (2, 180)]
meeting_duration = 30
day = 1
preference = True

print(schedule_meeting(shirley_schedule, albert_schedule, meeting_duration, day, preference))