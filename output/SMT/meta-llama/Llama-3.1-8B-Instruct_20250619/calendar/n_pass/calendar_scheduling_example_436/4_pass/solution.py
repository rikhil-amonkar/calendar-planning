from z3 import *

def find_meeting_time(participants, day, duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the start time variable
    start_time = [Int(f'start_time_{i}') for i in range(len(participants))]

    # Add constraints for the start and end time
    for i in range(len(participants)):
        solver.assert(start_time[i] >= 9*60)  # Changed the multiplication operator
        solver.assert(start_time[i] + duration <= 17*60)
        solver.assert(start_time[i] % 30 == 0)  # Meeting duration is 30 minutes

    # Add constraints for each participant
    for i, participant in enumerate(participants):
        for time in participant:
            for j in range(len(participants)):
                if i!= j:
                    # Check if the meeting time conflicts with the other participant's schedule
                    solver.assert(Or(start_time[i] >= time[0], start_time[i] + duration <= time[1]))

    # Solve the constraints
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        # Get the start time from the model
        start_time_value = model[start_time[0]].as_long()
        # Calculate the end time
        end_time_value = start_time_value + duration
        # Format the time
        day_str = day
        start_time_str = f'{start_time_value // 60:02d}:{start_time_value % 60:02d}'
        end_time_str = f'{end_time_value // 60:02d}:{end_time_value % 60:60}'
        # Return the solution
        return f'SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}'
    else:
        return 'No solution found'

# Define the participants' schedules
participants = [
    [(13 * 60, 14 * 60), (14.5 * 60, 15 * 60)],  # Patrick
    [(9 * 60, 9.5 * 60), (11 * 60, 11.5 * 60), (12 * 60, 12.5 * 60), (14.5 * 60, 15 * 60), (16 * 60, 17 * 60)],  # Shirley
    [(9 * 60, 9.5 * 60), (10.5 * 60, 11 * 60), (11.5 * 60, 12 * 60), (13 * 60, 13.5 * 60), (16 * 60, 17 * 60)],  # Jeffrey
    [(11.5 * 60, 12 * 60), (15 * 60, 15.5 * 60)],  # Gloria
    [(9 * 60, 9.5 * 60), (10.5 * 60, 12 * 60), (14 * 60, 17 * 60)],  # Nathan
    [(9 * 60, 9.5 * 60), (10 * 60, 11 * 60), (12.5 * 60, 15 * 60), (15.5 * 60, 16.5 * 60)],  # Angela
    [(9 * 60, 9.5 * 60), (10 * 60, 10.5 * 60), (11 * 60, 14 * 60), (14.5 * 60, 16.5 * 60)]  # David
]

# Find the meeting time
day = 'Monday'
duration = 30  # 30 minutes
solution = find_meeting_time(participants, day, duration)
print(solution)