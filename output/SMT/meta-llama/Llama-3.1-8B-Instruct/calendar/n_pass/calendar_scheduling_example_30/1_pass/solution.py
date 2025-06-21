from z3 import *

def schedule_meeting(jeffrey_schedule, virginia_schedule, melissa_schedule, meeting_duration, melissa_preference):
    # Define the day to meet
    day = 'Monday'

    # Define the start and end time variables
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for the start and end time
    constraints = [
        And(9*60 <= start_time, start_time <= 17*60),  # Within work hours
        And(start_time + meeting_duration <= 17*60),  # Meeting ends within work hours
        Or(start_time < 9*60, start_time + meeting_duration > 17*60)  # Meeting is not at the very start or end of the day
    ]

    # Add constraints for each participant's schedule
    for schedule in [jeffrey_schedule, virginia_schedule, melissa_schedule]:
        for time in schedule:
            constraints.append(And(time[0]*60 <= start_time, start_time < time[1]*60))

    # Add a constraint for Melissa's preference
    if melissa_preference:
        for time in melissa_schedule:
            if time[0]*60 <= 14*60 and time[1]*60 > 14*60:
                constraints.append(Not(start_time > 14*60))

    # Add a constraint to ensure the meeting duration
    constraints.append(start_time + meeting_duration == end_time)

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        start_hour = start_time_value // 60
        start_minute = start_time_value % 60
        end_hour = end_time_value // 60
        end_minute = end_time_value % 60
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_hour:02d}:{start_minute:02d}\nEnd Time: {end_hour:02d}:{end_minute:02d}'
    else:
        return 'No solution found'

# Example usage
jeffrey_schedule = [(9.5*60, 10*60), (10.5*60, 11*60)]
virginia_schedule = [(9*60, 9.5*60), (10*60, 10.5*60), (14.5*60, 15*60), (16*60, 16.5*60)]
melissa_schedule = [(9*60, 11.5*60), (12*60, 12.5*60), (13*60, 15*60), (16*60, 17*60)]
meeting_duration = 30
melissa_preference = True

print(schedule_meeting(jeffrey_schedule, virginia_schedule, melissa_schedule, meeting_duration, melissa_preference))