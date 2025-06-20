from z3 import *

def schedule_meeting(margaret_schedule, donna_schedule, helen_schedule, day, meeting_duration):
    # Create Z3 variables for the start time
    start_time = Int('start_time')
    
    # Ensure the start time is within the work hours
    is_within_work_hours = And(start_time >= 9, start_time <= 17)
    
    # Ensure the end time is within the work hours
    end_time = start_time + meeting_duration
    is_within_work_hours = And(is_within_work_hours, end_time <= 17)
    
    # Ensure the start time does not conflict with Margaret's schedule
    for start, end in margaret_schedule:
        is_not_conflicting = And(start_time + meeting_duration <= start, end_time >= end)
        is_within_work_hours = And(is_within_work_hours, is_not_conflicting)
    
    # Ensure the start time does not conflict with Donna's schedule
    for start, end in donna_schedule:
        is_not_conflicting = And(start_time + meeting_duration <= start, end_time >= end)
        is_within_work_hours = And(is_within_work_hours, is_not_conflicting)
    
    # Ensure the start time does not conflict with Helen's schedule
    for start, end in helen_schedule:
        is_not_conflicting = And(start_time + meeting_duration <= start, end_time >= end)
        is_within_work_hours = And(is_within_work_hours, is_not_conflicting)
    
    # Ensure Helen does not meet after 13:30
    is_not_conflicting = And(end_time <= 13 * 60 + 30)
    is_within_work_hours = And(is_within_work_hours, is_not_conflicting)
    
    # Solve the constraints
    solver = Solver()
    solver.add(is_within_work_hours)
    if solver.check() == sat:
        model = solver.model()
        return f'SOLUTION:\nDay: {day}\nStart Time: {model[start_time].as_long() // 60:02d}:{model[start_time].as_long() % 60:02d}\nEnd Time: {(model[start_time].as_long() // 60 + meeting_duration.as_long() // 60):02d}:{(model[start_time].as_long() % 60 + meeting_duration.as_long() % 60):02d}'
    else:
        return 'No solution found'

# Define the schedules
margaret_schedule = [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30)]
donna_schedule = [(14 * 60 + 30, 15 * 60), (16 * 60, 16 * 60 + 30)]
helen_schedule = [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 17 * 60)]

# Find a solution
print(schedule_meeting(margaret_schedule, donna_schedule, helen_schedule, 'Monday', 30 * 60))