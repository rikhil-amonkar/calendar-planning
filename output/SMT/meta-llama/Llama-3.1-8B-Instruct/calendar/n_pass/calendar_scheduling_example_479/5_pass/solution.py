YOUR_CODE
from z3 import *

def schedule_meeting(day, start_time, end_time, schedules):
    # Create a Z3 solver
    solver = Solver()

    # Define the meeting duration
    meeting_duration = 60

    # Add constraints for each participant
    for participant, schedule in schedules.items():
        # Add constraint that the meeting time does not conflict with the participant's schedule
        for time in schedule:
            # Check if the meeting time overlaps with the participant's schedule
            if (time[0] <= start_time + meeting_duration and start_time <= time[1]) or \
               (time[0] <= end_time and end_time <= time[1]) or \
               (start_time <= time[0] and time[1] <= end_time):
                # If the meeting time conflicts with the participant's schedule, add a constraint to the solver
                solver.assert_or(Not(start_time == time[0] + 30) | Not(end_time == time[1] - 30))

    # Add constraint that the meeting time is within the work hours
    solver.assert_and_list([start_time >= 9, end_time <= 17, start_time % 60 == 0, (end_time - start_time) == meeting_duration])

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        # Return the solution as a string
        return f"SOLUTION:\nDay: {day}\nStart Time: {model[start_time].as_string()}\nEnd Time: {model[end_time].as_string()}"
    else:
        # If no solution exists, return an error message
        return "No solution exists"

# Define the existing schedules for each participant
schedules = {
    'Evelyn': [],
    'Joshua': [(11, 12.5), (13.5, 14.5), (16.5, 17)],
    'Kevin': [],
    'Gerald': [],
    'Jerry': [(9, 9.5), (10.5, 12), (12.5, 13), (13.5, 14), (14.5, 15), (15.5, 16)],
    'Jesse': [(9, 9.5), (10.5, 12), (12.5, 13), (14.5, 15), (15.5, 16.5)],
    'Kenneth': [(10.5, 12.5), (13.5, 14), (14.5, 15), (15.5, 16), (16.5, 17)]
}

# Define the meeting duration
meeting_duration = 60

# Define the start and end times as Z3 variables
day = 'Monday'
start_time = Int('start_time')
end_time = Int('end_time')

# Define the solver
solver = Solver()

# Add constraint that the meeting time is within the work hours
solver.assert_and_list([start_time >= 9, end_time <= 17, start_time % 60 == 0, (end_time - start_time) == meeting_duration])

# Add constraint that the meeting time does not conflict with any participant's schedule
for participant, schedule in schedules.items():
    # Add constraint that the meeting time does not conflict with the participant's schedule
    for time in schedule:
        # Check if the meeting time overlaps with the participant's schedule
        if (time[0] <= start_time + meeting_duration and start_time <= time[1]) or \
           (time[0] <= end_time and end_time <= time[1]) or \
           (start_time <= time[0] and time[1] <= end_time):
            # If the meeting time conflicts with the participant's schedule, add a constraint to the solver
            solver.assert_or(Not(start_time == time[0] + 30) | Not(end_time == time[1] - 30))

# Check if a solution exists
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    # Return the solution as a string
    print(schedule_meeting(day, model[start_time].as_long(), model[end_time].as_long(), schedules))
else:
    # If no solution exists, return an error message
    print("No solution exists")

print("\n")