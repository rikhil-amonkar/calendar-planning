from z3 import *

def schedule_meeting(schedules, duration):
    # Create a Z3 solver
    solver = Solver()

    # Create variables for the start time
    start_time = [Int(f'start_time_{i}') for i in range(len(schedules))]

    # Create variables for the end time
    end_time = [start_time[i] + duration for i in range(len(schedules))]

    # Add constraints for each participant
    for i, (name, schedule) in enumerate(schedules.items()):
        for time in schedule:
            # Convert time to minutes
            start, end = time.split('-')
            start = int(start[0:2]) * 60 + int(start[3:5])
            end = int(end[0:2]) * 60 + int(end[3:5])

            # Add constraints for each time slot
            for j in range(start, end):
                # Check if the meeting time overlaps with the participant's schedule
                solver.assert(And(start_time[i] < j, j < end_time[i]))

    # Add constraints for the meeting duration
    for i in range(len(schedules)):
        solver.assert(And(start_time[i] >= 9 * 60, start_time[i] + duration < 17 * 60))

    # Check if a solution exists
    if solver.check() == sat:
        # Get the model
        model = solver.model()

        # Extract the start and end times
        start_time_value = model[start_time[0]].as_long()
        end_time_value = start_time_value + duration

        # Format the output
        day = 'Monday'
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}'
    else:
        return 'No solution exists'

# Define the schedules
schedules = {
    'Andrea': ['09:30-10:30', '13:30-14:30'],
    'Ruth': ['12:30-13:00', '15:00-15:30'],
    'Steven': ['10:00-10:30', '11:00-11:30', '12:00-12:30', '13:30-14:00', '15:00-16:00'],
    'Grace': [],
    'Kyle': ['09:00-09:30', '10:30-12:00', '12:30-13:00', '13:30-15:00', '15:30-16:00', '16:30-17:00'],
    'Elijah': ['09:00-11:00', '11:30-13:00', '13:30-14:00', '15:30-16:00', '16:30-17:00'],
    'Lori': ['09:00-09:30', '10:00-11:30', '12:00-13:30', '14:00-16:00', '16:30-17:00']
}

# Define the meeting duration
duration = 30

# Print the solution
print(schedule_meeting(schedules, duration))