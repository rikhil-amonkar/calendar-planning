from z3 import *

def schedule_meeting(schedules, meeting_duration):
    # Define the day and time intervals
    day = 'Monday'
    start_time = 9 * 60
    end_time = 17 * 60

    # Create a list of participants and their available times
    participants = ['Jacob', 'Diana', 'Adam', 'Angela', 'Dennis']
    times = []
    for participant in participants:
        participant_times = []
        for time in schedules[participant]:
            start, end = time
            start, end = start * 60, end * 60
            participant_times.append((start, end))
        times.append(participant_times)

    # Create Z3 variables for the start and end times of the meeting
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')

    # Create Z3 constraints for the meeting duration and time intervals
    constraints = [
        And(start_time_var >= start_time, start_time_var <= end_time),
        And(end_time_var >= start_time_var, end_time_var <= end_time),
        And(end_time_var - start_time_var == meeting_duration * 60)
    ]

    # Create Z3 variables for the available times of each participant
    participant_vars = [Int(f'participant_{i}') for i in range(len(participants))]

    # Create Z3 constraints for the available times of each participant
    for i, participant_times in enumerate(times):
        for start, end in participant_times:
            start, end = start * 60, end * 60
            constraints.append(Or(
                start_time_var + meeting_duration * 60 > end,
                start_time_var < start,
                end_time_var <= start
            ))

    # Create Z3 variables for the start and end times of each time slot
    time_slot_vars = [Int(f'time_slot_{i}') for i in range(len(participants) + 2)]

    # Create Z3 constraints for the time slots
    for i in range(len(participants) + 1):
        constraints.append(And(
            time_slot_vars[i] >= start_time,
            time_slot_vars[i] <= end_time,
            If(i < len(participants), time_slot_vars[i + 1] > time_slot_vars[i] + meeting_duration * 60, time_slot_vars[i + 1] == end_time)
        ))

    # Create Z3 constraints for the meeting time
    constraints.append(And(
        start_time_var == time_slot_vars[0],
        end_time_var == time_slot_vars[1]
    ))

    # Create Z3 variables for the meeting time slots
    meeting_time_slot_vars = [Int(f'meeting_time_slot_{i}') for i in range(2)]

    # Create Z3 constraints for the meeting time slots
    for i in range(2):
        constraints.append(And(
            meeting_time_slot_vars[i] >= start_time,
            meeting_time_slot_vars[i] <= end_time,
            If(i < 1, meeting_time_slot_vars[i + 1] > meeting_time_slot_vars[i] + meeting_duration * 60, meeting_time_slot_vars[i + 1] == end_time)
        ))

    # Create Z3 constraints for the meeting time
    constraints.append(And(
        start_time_var == meeting_time_slot_vars[0],
        end_time_var == meeting_time_slot_vars[1]
    ))

    # Solve the Z3 constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time_var].as_long()
        end_time_value = model[end_time_var].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}"
    else:
        return "No solution found"

# Existing schedules for everyone during the day
schedules = {
    'Jacob': [(13.5, 14), (14.5, 15)],
    'Diana': [(9.5, 10), (11.5, 12), (13, 13.5), (16, 16.5)],
    'Adam': [(9.5, 10.5), (11, 12.5), (15.5, 16)],
    'Angela': [(9.5, 10), (10.5, 12), (13, 15.5), (16, 16.5)],
    'Dennis': [(9, 9.5), (10.5, 11.5), (13, 15), (16.5, 17)]
}

# Meeting duration (in hours)
meeting_duration = 0.5

print(schedule_meeting(schedules, meeting_duration))