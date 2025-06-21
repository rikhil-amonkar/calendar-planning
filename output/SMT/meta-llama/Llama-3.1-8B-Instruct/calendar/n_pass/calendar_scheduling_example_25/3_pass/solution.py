from z3 import *

def schedule_meeting(anthony_schedule, pamela_schedule, zachary_schedule, meeting_duration, pamela_preference):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end times of the meeting
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for the start and end times
    constraints = [
        And(9*60 <= start_time, start_time <= 17*60),  # Meeting time between 9:00 and 17:00
        start_time + meeting_duration*60 <= 17*60,  # Meeting duration is 1 hour
        start_time >= 10*60  # Start time is at least 10 minutes past the hour
    ]

    # Add constraints for each participant's schedule
    for start, end in anthony_schedule:
        constraints.append(Or(start*60 + meeting_duration*60 > end*60, start*60 > end*60))
    for start, end in pamela_schedule:
        constraints.append(Or(start*60 + meeting_duration*60 > end*60, start*60 > end*60))
    for start, end in zachary_schedule:
        constraints.append(Or(start*60 + meeting_duration*60 > end*60, start*60 > end*60))

    # Add constraint for Pamela's preference
    if pamela_preference:
        constraints.append(start_time < 14*60 + 30*60)

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}'
    else:
        return 'No solution found'

# Example usage
anthony_schedule = [(9*60 + 30*60, 10*60), (12*60, 13*60), (16*60, 16*60 + 30*60)]
pamela_schedule = [(9*60 + 30*60, 10*60), (16*60 + 30*60, 17*60)]
zachary_schedule = [(9*60, 11*60 + 30*60), (12*60, 12*60 + 30*60), (13*60, 13*60 + 30*60), (14*60 + 30*60, 15*60), (16*60, 17*60)]
meeting_duration = 1
pamela_preference = True

print(schedule_meeting(anthony_schedule, pamela_schedule, zachary_schedule, meeting_duration, pamela_preference))