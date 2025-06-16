from z3 import *

def schedule_meeting(adam_schedule, roy_schedule, meeting_duration):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end time of the work hours
    start_time = 9
    end_time = 17

    # Create a Z3 solver
    solver = Solver()

    # Define the possible start times for the meeting
    start_times = [i for i in range(start_time, end_time - meeting_duration + 1)]

    # Define the variables for the start and end time of the meeting
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')

    # Add the constraints for the start and end time
    solver.add(And(start_time <= start_time_var, start_time_var <= end_time))
    solver.add(And(start_time_var + meeting_duration <= end_time, end_time_var <= end_time))

    # Define the constraints for Adam's schedule
    adam_busy_intervals = [(9*60 + 30, 10*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60), (16*60 + 30, 17*60)]
    for start, end in adam_busy_intervals:
        solver.add(Or(start_time_var < start, end_time_var > end))

    # Define the constraints for Roy's schedule
    roy_busy_intervals = [(10*60, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (16*60 + 30, 17*60)]
    for start, end in roy_busy_intervals:
        solver.add(Or(start_time_var < start, end_time_var > end))

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_time_val = model[start_time_var].as_long()
        end_time_val = model[end_time_var].as_long()

        # Return the solution
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}\nEnd Time: {(start_time_val + meeting_duration) // 60:02d}:{(start_time_val + meeting_duration) % 60:02d}"
    else:
        return "No solution exists"

# Example usage:
adam_schedule = [(9*60 + 30, 10*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60), (16*60 + 30, 17*60)]
roy_schedule = [(10*60, 11*60), (11*60 + 30, 13*60), (13*60 + 30, 14*60 + 30), (16*60 + 30, 17*60)]
meeting_duration = 30

print(schedule_meeting(adam_schedule, roy_schedule, meeting_duration))