from z3 import *

def find_meeting_time(day, participants, schedules, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define variables for each participant's availability
    availability = [Bool(f'available_{i}') for i in range(len(participants))]

    # Define variables for the start time
    start_time = Int('start_time')

    # Define a variable for the end time
    end_time = start_time + meeting_duration

    # Add constraints for each participant's availability
    for i, participant in enumerate(participants):
        for start, end in schedules[participant]:
            solver.add(Not(And(And(start_time >= start, start_time < end),
                              And(end_time > start, end_time <= end))))

    # Add constraint that all participants are available at the meeting time
    for i, participant in enumerate(participants):
        if schedules[participant]:
            for start, end in schedules[participant]:
                if start < end_time and end_time < end:
                    solver.add(False)
                    break
        else:
            solver.add(True)

    # Add constraint that the meeting duration is exactly 0.5 hours
    solver.add(end_time - start_time == meeting_duration)

    # Add constraint that the meeting time is within the work hours
    solver.add(And(start_time >= 9, end_time <= 17))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        return f'SOLUTION:\nDay: {day}\nStart Time: {model[start_time].as_long():02d}:{(model[start_time].as_long() % 60):02d}\nEnd Time: {model[end_time].as_long():02d}:{(model[end_time].as_long() % 60):02d}'
    else:
        return 'No solution found'

# Define the schedules for each participant
schedules = {
    'Gregory': [(9, 10), (10.5, 11.5), (12.5, 13), (13.5, 14)],
    'Natalie': [],
    'Christine': [(9, 11.5), (13.5, 17)],
    'Vincent': [(9, 9.5), (10.5, 12), (12.5, 14), (14.5, 17)]
}

# Find a meeting time that works for everyone
print(find_meeting_time('Monday', ['Gregory', 'Natalie', 'Christine', 'Vincent'], schedules, 30))