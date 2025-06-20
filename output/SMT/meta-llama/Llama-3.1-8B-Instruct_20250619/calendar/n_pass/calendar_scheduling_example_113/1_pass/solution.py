from z3 import *

def schedule_meeting(participants, duration):
    # Define the day and time slots
    day = 'Monday'
    start_time = 9 * 60
    end_time = 17 * 60
    time_slots = [i for i in range(start_time, end_time)]

    # Create Z3 variables for each participant
    participant_vars = {}
    for participant in participants:
        participant_vars[participant] = [Bool(f'{participant}_available_{i}') for i in time_slots]

    # Create Z3 variables for the meeting start time
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define constraints for each participant
    constraints = []
    for participant, vars in participant_vars.items():
        for i, var in enumerate(vars):
            constraints.append(Or(var, meeting_start + duration > i + start_time))
        constraints.append(Not(var) | (meeting_start + duration <= i + start_time))

    # Define constraints for the meeting duration
    constraints.append(meeting_start + duration <= end_time)
    constraints.append(meeting_end == meeting_start + duration)

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    solver.add(Or([participant_vars[participant][i] for participant, vars in participant_vars.items() for i in range(len(vars))]))
    if solver.check() == sat:
        model = solver.model()
        meeting_start_val = model[meeting_start].as_long()
        meeting_end_val = model[meeting_end].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {meeting_start_val // 60:02d}:{meeting_start_val % 60:02d}\nEnd Time: {meeting_end_val // 60:02d}:{meeting_end_val % 60:02d}'
    else:
        return 'No solution found'

# Define the participants and their schedules
participants = ['Bradley', 'Teresa', 'Elizabeth', 'Christian']
schedules = {
    'Bradley': [(9 * 60 + 30, 10 * 60), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (15 * 60 + 30, 16 * 60)],
    'Teresa': [(10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)],
    'Elizabeth': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 17 * 60)],
    'Christian': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 17 * 60)]
}

# Find a time that works for everyone
duration = 30 * 60
print(schedule_meeting(participants, duration))