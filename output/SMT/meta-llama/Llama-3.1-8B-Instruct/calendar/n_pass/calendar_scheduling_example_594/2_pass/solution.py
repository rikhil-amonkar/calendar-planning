from z3 import *

def schedule_meeting(adam_schedule, roy_schedule, meeting_duration):
    """
    Schedules a meeting between Adam and Roy.

    Args:
    adam_schedule (list): Adam's schedule as a list of tuples (start_time, end_time).
    roy_schedule (list): Roy's schedule as a list of tuples (start_time, end_time).
    meeting_duration (int): The duration of the meeting in hours.

    Returns:
    str: A string describing the scheduled meeting in the format 'SOLUTION:\nDay: <day>\nStart Time: <HH:MM>\nEnd Time: <HH:MM>'.
    """
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end times of the meeting
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the constraints for the start and end times
    constraints = [
        And(start_time >= 9*60, start_time < 17*60),  # Between 9:00 and 17:00
        And(end_time > start_time, end_time - start_time == meeting_duration * 60),  # Meeting duration
    ]

    # Define the constraints for Adam's schedule
    adam_constraints = [
        Or(start_time >= 9*60 + 30, start_time < 9*60 + 30 + 30),  # Not between 9:30 and 10:00
        Or(start_time >= 12*60 + 30, start_time < 12*60 + 30 + 30),  # Not between 12:30 and 13:00
        Or(start_time >= 14*60 + 30, start_time < 14*60 + 30 + 30),  # Not between 14:30 and 15:00
        Or(start_time >= 16*60 + 30, start_time < 16*60 + 30 + 30),  # Not between 16:30 and 17:00
    ]

    # Define the constraints for Roy's schedule
    roy_constraints = [
        Or(start_time >= 10*60, start_time < 10*60 + 60),  # Not between 10:00 and 11:00
        Or(start_time >= 11*60 + 30, start_time < 11*60 + 30 + 90),  # Not between 11:30 and 13:00
        Or(start_time >= 13*60 + 30, start_time < 13*60 + 30 + 60),  # Not between 13:30 and 14:30
        Or(start_time >= 16*60 + 30, start_time < 16*60 + 30 + 30),  # Not between 16:30 and 17:00
    ]

    # Add the constraints to the solver
    solver = Solver()
    solver.add(constraints + adam_constraints + roy_constraints)

    # Check if there is a solution
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        # Extract the start and end times
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        # Format the times as strings
        start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'
        end_time_str = f'{end_time_value // 60:02d}:{end_time_value % 60:02d}'
        # Return the solution
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}'
    else:
        # Return a message indicating that there is no solution
        return 'No solution found'

# Define the schedules for Adam and Roy
adam_schedule = [(9*60 + 30, 9*60 + 30 + 30), (12*60 + 30, 12*60 + 30 + 30), (14*60 + 30, 14*60 + 30 + 30), (16*60 + 30, 16*60 + 30 + 30)]
roy_schedule = [(10*60, 10*60 + 60), (11*60 + 30, 11*60 + 30 + 90), (13*60 + 30, 13*60 + 30 + 60), (16*60 + 30, 16*60 + 30 + 30)]

# Define the meeting duration
meeting_duration = 0.5

# Schedule the meeting
solution = schedule_meeting(adam_schedule, roy_schedule, meeting_duration)
print(solution)