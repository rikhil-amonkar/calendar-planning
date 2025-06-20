from z3 import *

def schedule_meeting():
    # Define the day of the meeting
    day = "Monday"

    # Define the meeting duration
    meeting_duration = 30  # minutes

    # Define the start and end time of the work hours
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes

    # Define the existing schedules for each participant
    gregory_schedule = [9 * 60, 10 * 60, 10 * 30, 11 * 30, 12 * 30, 13 * 30, 14 * 30]
    natalie_schedule = []
    christine_schedule = [9 * 60, 11 * 30, 13 * 30, 17 * 60]
    vincent_schedule = [9 * 30, 10 * 30, 12 * 30, 14 * 30, 17 * 60]

    # Create Z3 variables for the start time of the meeting
    start_time_var = Int('start_time')

    # Define the constraints for the start time of the meeting
    constraints = [
        And(start_time_var >= start_time, start_time_var <= end_time - meeting_duration),
        start_time_var + meeting_duration <= end_time
    ]

    # Define the constraints for each participant's schedule
    for schedule in [gregory_schedule, christine_schedule, vincent_schedule]:
        for time in schedule:
            constraints.append(Or(start_time_var + meeting_duration > time, start_time_var + meeting_duration < time))

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time_var].as_long()
        end_time_value = start_time_value + meeting_duration
        print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}")
    else:
        print("No solution found")

schedule_meeting()