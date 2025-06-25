from z3 import *

def schedule_meeting(participants, duration):
    # Define the day
    day = 'Monday'

    # Define the start and end time
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60  # 17:00 in minutes
    duration_minutes = int(duration * 60)  # Convert duration to minutes

    # Create a boolean variable for each time slot
    time_slots = [Bool(f'time_slot_{i}') for i in range((end_time - start_time) // 60 + 1)]

    # Create a constraint for each participant
    constraints = []
    for participant, schedule in participants.items():
        for time in schedule:
            start = time[0] * 60
            end = time[1] * 60
            for i in range(start, end):
                constraints.append(Not(time_slots[i]))

    # Add the constraint that the meeting must last for at least the given duration
    for i in range(len(time_slots) - duration_minutes + 1):
        constraints.append(Or([time_slots[j] for j in range(i, i + duration_minutes)]))

    # Add the constraint that the meeting must start before the end time
    for i in range(len(time_slots) - duration_minutes):
        constraints.append(And(time_slots[i], Not(time_slots[i + duration_minutes])))

    # Add the constraint that the meeting must start after the start time
    for i in range(duration_minutes):
        constraints.append(Not(time_slots[i]))

    # Solve the constraints
    solver = Solver()
    for constraint in constraints:
        solver.add(constraint)
    if solver.check() == sat:
        model = solver.model()
        for i, slot in enumerate(model.evaluate(time_slots)):
            if slot:
                start_time_index = i
                break
        if start_time_index is None:
            return 'No solution found'
        end_time_index = start_time_index + duration_minutes
        if end_time_index > len(time_slots) - 1:
            return 'No solution found'
        start_time_minutes = start_time_index
        end_time_minutes = end_time_index
        start_time_hours = start_time_minutes // 60
        start_time_minutes %= 60
        end_time_hours = end_time_minutes // 60
        end_time_minutes %= 60
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_hours:02d}:{start_time_minutes:02d}\nEnd Time: {end_time_hours:02d}:{end_time_minutes:02d}'
    else:
        return 'No solution found'

# Define the participants and their schedules
participants = {
    'Ronald': [],
    'Stephen': [(10 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30)],
    'Brittany': [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    'Dorothy': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
    'Rebecca': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)],
    'Jordan': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)]
}

# Define the meeting duration
duration = 0.5

print(schedule_meeting(participants, duration))