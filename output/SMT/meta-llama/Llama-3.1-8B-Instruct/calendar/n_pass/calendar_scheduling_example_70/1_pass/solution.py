from z3 import *

def schedule_meeting(denise_schedule, angela_schedule, natalie_schedule, meeting_duration):
    # Define the variables
    day = 'Monday'
    start_time = Int('start_time')
    end_time = start_time + meeting_duration
    
    # Define the constraints
    constraints = [
        # Denise is busy during these times
        Or(start_time >= 12, start_time + meeting_duration <= 12),
        Or(start_time >= 15.5, start_time + meeting_duration <= 15.5),
        
        # Angela is not busy at all
        start_time >= 24,
        end_time <= 0,
        
        # Natalie is busy during these times
        Or(start_time >= 9, start_time + meeting_duration <= 9),
        Or(start_time >= 11.5, start_time + meeting_duration <= 11.5),
        Or(start_time >= 12, start_time + meeting_duration <= 12),
        Or(start_time >= 13.5, start_time + meeting_duration <= 13.5),
        Or(start_time >= 14, start_time + meeting_duration <= 14),
        Or(start_time >= 15, start_time + meeting_duration <= 15),
        Or(start_time >= 17, start_time + meeting_duration <= 17),
        
        # Meeting duration
        start_time >= 0,
        end_time <= 17,
        
        # Start time and end time are in the correct order
        start_time <= end_time
    ]
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value:02d}:00\nEnd Time: {end_time_value:02d}:00'
    else:
        return 'No solution found'

# Test the function
denise_schedule = [12, 12.5, 15.5, 16]
angela_schedule = [0, 24]
natalie_schedule = [9, 11.5, 12, 13.5, 14, 15, 17]
meeting_duration = 0.5

print(schedule_meeting(denise_schedule, angela_schedule, natalie_schedule, meeting_duration))