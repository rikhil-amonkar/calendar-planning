from z3 import *

def schedule_meeting(diane_blocked, jack_blocked, eugene_blocked, patricia_blocked, meeting_duration):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start time of the meeting
    start_time = Int('start_time')

    # Define the constraints for the start time
    constraints = [
        And(9 * 60 <= start_time, start_time <= 17 * 60),  # Meeting time is between 9:00 and 17:00
        start_time % 60 == 0,  # Start time is on the hour
        start_time + meeting_duration <= 17 * 60  # Meeting duration is less than or equal to 17:00
    ]

    # Define the constraints for each participant's blocked times
    for blocked in [diane_blocked, jack_blocked, eugene_blocked, patricia_blocked]:
        for i in range(0, len(blocked), 2):
            constraints.append(Or(start_time + meeting_duration > blocked[i] + blocked[i+1], 
                                  start_time + meeting_duration < blocked[i]))

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_val = model[start_time].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}\nEnd Time: {(start_time_val // 60 + 1) * 60 + (start_time_val % 60 + meeting_duration) % 60:02d}:{((start_time_val // 60 + 1) * 60 + (start_time_val % 60 + meeting_duration) % 60) % 60:02d}'
    else:
        return 'No solution found'

# Define the blocked times for each participant
diane_blocked = [9 * 60 + 30, 10 * 60, 14 * 60 + 30, 15 * 60]
jack_blocked = [13 * 60 + 30, 14 * 60, 14 * 60 + 30, 15 * 60]
eugene_blocked = [9 * 60, 10 * 60, 10 * 60 + 30, 11 * 60 + 30, 12 * 60, 14 * 60 + 30, 15 * 60, 16 * 60 + 30]
patricia_blocked = [9 * 60 + 30, 10 * 60 + 30, 11 * 60, 12 * 60, 12 * 60 + 30, 14 * 60, 15 * 60, 16 * 60 + 30]

# Define the meeting duration
meeting_duration = 30

print(schedule_meeting(diane_blocked, jack_blocked, eugene_blocked, patricia_blocked, meeting_duration))