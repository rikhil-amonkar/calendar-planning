from z3 import *

def schedule_meeting(patrick_schedules, kayla_schedules, carl_schedules, christian_schedules, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the day of the meeting
    day = Bool('day')
    solver.add(day)

    # Define the start time of the meeting
    start_time = Int('start_time')
    solver.add(9 <= start_time)
    solver.add(start_time <= 17)
    solver.add(start_time % 30 == 0)  # Meeting duration is half an hour

    # Define the end time of the meeting
    end_time = start_time + meeting_duration

    # Add constraints based on existing schedules
    for schedule in [patrick_schedules, kayla_schedules, carl_schedules, christian_schedules]:
        for time in schedule:
            if time[0] <= start_time <= time[1]:
                solver.add(False)  # Conflict, add a contradiction
            if time[0] <= end_time <= time[1]:
                solver.add(False)

    # Solve the constraints
    solver.check()

    # Get the solution
    if solver.model():
        start_hour = solver.model()[start_time].as_long() // 60
        start_minute = solver.model()[start_time].as_long() % 60
        end_hour = solver.model()[end_time].as_long() // 60
        end_minute = solver.model()[end_time].as_long() % 60
        return f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02d}:{start_minute:02d}\nEnd Time: {end_hour:02d}:{end_minute:02d}"
    else:
        return "No solution found"

# Existing schedules
patrick_schedules = [(9, 9.5), (10, 10.5), (13.5, 14), (16, 16.5)]
kayla_schedules = [(12.5, 13.5), (15, 15.5), (16, 16.5)]
carl_schedules = [(10.5, 11), (12, 12.5), (13, 13.5), (14.5, 17)]
christian_schedules = [(9, 12.5), (13, 14), (14.5, 17)]

# Meeting duration (half an hour)
meeting_duration = 30

# Call the function
print(schedule_meeting(patrick_schedules, kayla_schedules, carl_schedules, christian_schedules, meeting_duration))