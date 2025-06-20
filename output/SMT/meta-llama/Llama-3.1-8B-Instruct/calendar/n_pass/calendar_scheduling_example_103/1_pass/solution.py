from z3 import *

def schedule_meeting(participants, meeting_duration):
    # Define the time slots
    start_time = 9 * 60  # 9:00
    end_time = 17 * 60  # 17:00
    time_slots = [i for i in range(start_time, end_time, 30)]  # 30-minute intervals

    # Define the variables
    day = 'Monday'
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints
    constraints = [
        And(meeting_start >= start_time, meeting_start <= end_time),
        And(meeting_end >= start_time, meeting_end <= end_time),
        meeting_end - meeting_start == meeting_duration,
    ]

    # Add constraints for each participant
    for participant, schedule in participants.items():
        for time in schedule:
            constraints.append(Or(meeting_start + i >= time + 60 for i in range(30) if meeting_start + i <= time + 60))
            constraints.append(Or(meeting_end + i >= time + 60 for i in range(30) if meeting_end + i <= time + 60))

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        meeting_start_val = model[meeting_start].as_long()
        meeting_end_val = model[meeting_end].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {meeting_start_val // 60:02d}:{meeting_start_val % 60:02d}\nEnd Time: {meeting_end_val // 60:02d}:{meeting_end_val % 60:02d}"
    else:
        return "No solution found"

# Define the participants and their schedules
participants = {
    'Diane': [9 * 60 + 30, 14 * 60 + 30],
    'Jack': [13 * 60 + 30, 14 * 60 + 30],
    'Eugene': [9 * 60, 10 * 60, 10 * 60 + 30, 12 * 60, 14 * 60 + 30, 15 * 60],
    'Patricia': [9 * 60 + 30, 10 * 60 + 30, 11 * 60, 12 * 60 + 30, 14 * 60 + 30, 15 * 60],
}

# Define the meeting duration
meeting_duration = 30  # 30 minutes

# Print the solution
print(schedule_meeting(participants, meeting_duration))