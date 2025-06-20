from z3 import *

def schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, preferences=None):
    # Create a Z3 solver
    solver = Solver()

    # Define the day
    day = 'Monday'

    # Define the start and end times
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for the start time
    solver.add(9 <= start_time)
    solver.add(start_time <= 17)

    # Add constraints for the end time
    solver.add(end_time <= 17)
    solver.add(end_time >= 9)

    # Add constraints for the meeting duration
    solver.add(end_time - start_time == meeting_duration)

    # Add constraints for Jack's schedule
    for start, end in jack_schedule:
        solver.add(And(start <= start_time, end >= start_time))

    # Add constraints for Charlotte's schedule
    for start, end in charlotte_schedule:
        solver.add(And(start <= start_time, end >= start_time))

    # Add preferences for Jack
    if preferences and 'avoid_after' in preferences and preferences['avoid_after']:
        solver.add(start_time <= 12)

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        # Extract the start and end times
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        # Return the solution as a string
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value:02d}:{(start_time_value % 100):02d}\nEnd Time: {end_time_value:02d}:{(end_time_value % 100):02d}'
    else:
        return 'No solution found'

# Example usage
jack_schedule = [(9*60+30, 9*60+60), (10*60+0, 10*60+30), (11*60+0, 11*60+30), (12*60+30, 12*60+60), (16*60+0, 16*60+30)]
charlotte_schedule = [(9*60+30, 9*60+60), (10*60+30, 12*60+0), (12*60+30, 13*60+30), (14*60+0, 16*60+0)]
meeting_duration = 30
preferences = {'avoid_after': True}

print(schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, preferences))