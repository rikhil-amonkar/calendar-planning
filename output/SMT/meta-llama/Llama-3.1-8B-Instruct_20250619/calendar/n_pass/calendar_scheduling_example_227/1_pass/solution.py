from z3 import *

def schedule_meeting(participants, meeting_duration, preferences):
    # Define the day and time slots
    day = 'Monday'
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes
    time_slots = [i for i in range(start_time, end_time - meeting_duration + 1)]

    # Define the variables
    meeting_start = [Int(f'meeting_start_{i}') for i in range(len(participants))]
    for i in range(len(participants)):
        meeting_start[i].sort(IntSort())
        meeting_start[i].get_sort().set_range(IntSort(0, len(time_slots) - 1))

    # Define the constraints
    constraints = []
    for i in range(len(participants)):
        constraints.append(And(meeting_start[i] >= start_time, meeting_start[i] <= end_time - meeting_duration))
        for j, participant in enumerate(participants):
            if i!= j:
                constraints.append(Or(meeting_start[i] < participants[j]['start'] - meeting_duration,
                                      meeting_start[i] >= participants[j]['end']))
        if preferences and i == participants.index(preferences):
            constraints.append(meeting_start[i] >= 14 * 60)

    # Define the solver
    solver = Solver()
    for var in meeting_start:
        solver.add(var >= 0)
    solver.add(And([meeting_start[i] + meeting_duration <= end_time for i in range(len(participants))]))

    # Add the constraints to the solver
    for constraint in constraints:
        solver.add(constraint)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        start_time = model[meeting_start[0]].as_long() // 60
        end_time = (model[meeting_start[0]].as_long() // 60) + meeting_duration // 60
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:{(start_time % 1) * 60:02d}\nEnd Time: {end_time:02d}:{(end_time % 1) * 60:02d}'
    else:
        return 'No solution found'

# Define the participants and their schedules
participants = [
    {'name': 'Natalie','start': 0, 'end': 17 * 60},
    {'name': 'David','start': 11 * 60, 'end': 12 * 60,'start2': 14 * 60 + 30, 'end2': 15 * 60},
    {'name': 'Douglas','start': 9 * 60 + 30, 'end': 10 * 60,'start2': 11 * 60, 'end2': 12 * 60,'start3': 13 * 60, 'end3': 13 * 60 + 30,'start4': 14 * 60 + 30, 'end4': 15 * 60},
    {'name': 'Ralph','start': 9 * 60, 'end': 9 * 60 + 30,'start2': 10 * 60, 'end2': 11 * 60,'start3': 11 * 60, 'end3': 12 * 60 + 30,'start4': 13 * 60 + 30, 'end4': 15 * 60,'start5': 15 * 60 + 30, 'end5': 16 * 60,'start6': 16 * 60 + 30, 'end6': 17 * 60},
    {'name': 'Jordan','start': 9 * 60, 'end': 10 * 60,'start2': 12 * 60, 'end2': 12 * 60 + 30,'start3': 13 * 60, 'end3': 13 * 60 + 30,'start4': 14 * 60 + 30, 'end4': 15 * 60,'start5': 15 * 60 + 30, 'end5': 17 * 60}
]

# Define the meeting duration and preferences
meeting_duration = 30
preferences = 'David'

print(schedule_meeting(participants, meeting_duration, preferences))