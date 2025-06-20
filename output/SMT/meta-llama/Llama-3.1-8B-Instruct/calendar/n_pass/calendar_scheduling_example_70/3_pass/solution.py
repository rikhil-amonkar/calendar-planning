from z3 import *

def schedule_meeting(denise_schedule, angela_schedule, natalie_schedule, meeting_duration):
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    
    # Define the constraints
    constraints = [
        # Denise is busy during these times
        And(And(start_time >= 12, start_time + meeting_duration * 60 <= 12.5 * 60),
            And(start_time >= 15.5 * 60, start_time + meeting_duration * 60 <= 16 * 60)),
        
        # Angela is not busy at all
        start_time >= 9 * 60,
        start_time + meeting_duration * 60 <= 17 * 60,
        
        # Natalie is busy during these times
        Or(start_time >= 9 * 60, start_time + meeting_duration * 60 <= 11.5 * 60),
        Or(start_time >= 11.5 * 60, start_time + meeting_duration * 60 <= 12 * 60),
        Or(start_time >= 12 * 60, start_time + meeting_duration * 60 <= 13 * 60),
        Or(start_time >= 13 * 60, start_time + meeting_duration * 60 <= 14 * 60),
        Or(start_time >= 14 * 60, start_time + meeting_duration * 60 <= 14.5 * 60),
        Or(start_time >= 14.5 * 60, start_time + meeting_duration * 60 <= 15 * 60),
        Or(start_time >= 15 * 60, start_time + meeting_duration * 60 <= 17 * 60),
        
        # Meeting duration
        start_time >= 0,
        start_time + meeting_duration * 60 <= 17 * 60,
        
        # Start time and end time are in the correct order
        start_time <= start_time + meeting_duration * 60
    ]
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = start_time_value + int(meeting_duration * 60)
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}'
    else:
        return 'No solution found'

# Test the function
denise_schedule = [12, 12.5, 15.5, 16]
angela_schedule = [0, 24]
natalie_schedule = [9, 11.5, 12, 13, 14, 14.5, 15, 17]
meeting_duration = 0.5

print(schedule_meeting(denise_schedule, angela_schedule, natalie_schedule, meeting_duration))