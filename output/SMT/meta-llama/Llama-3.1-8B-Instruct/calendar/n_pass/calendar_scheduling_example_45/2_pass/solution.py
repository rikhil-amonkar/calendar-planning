from z3 import *

def schedule_meeting(day, start_time, end_time, schedules):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables for the meeting time
    meeting_start = Int('meeting_start')

    # Add constraints for the meeting time
    solver.add(meeting_start >= start_time)
    solver.add(meeting_start + 30 <= end_time)

    # Add constraints for each participant's schedule
    for participant, schedule in schedules.items():
        # Check if the meeting time conflicts with the participant's schedule
        for time in schedule:
            solver.add(meeting_start + 30 <= time[0] or meeting_start >= time[1])

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        # Extract the meeting time from the solution
        meeting_start_value = model[meeting_start].as_long()
        # Calculate the end time
        meeting_end_value = meeting_start_value + 30
        # Format the output
        output = f'SOLUTION:\nDay: {day}\nStart Time: {meeting_start_value:02d}:00\nEnd Time: {meeting_end_value:02d}:30'
    else:
        output = 'No solution exists'

    return output


# Define the schedules for each participant
schedules = {
    'Andrew': [],
    'Grace': [],
    'Samuel': [(9, 10.5), (10.5, 11), (11, 11.5), (11.5, 12), (12, 13), (13, 13.5), (13.5, 14), (14, 16), (16, 16.5), (16.5, 17)]
}

# Define the day and time range
day = 'Monday'
start_time = 9
end_time = 17

# Call the function to schedule the meeting
print(schedule_meeting(day, start_time, end_time, schedules))