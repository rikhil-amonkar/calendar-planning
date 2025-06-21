from z3 import *

def schedule_meeting(diane_blocked, jack_blocked, eugene_blocked, patricia_blocked, meeting_duration):
    # Define the day of the meeting
    day = 'Monday'

    # Define the possible start times
    possible_start_times = []
    for hour in range(9, 17):
        possible_start_times.append(hour * 60)

    # Define the constraints for each participant's blocked times
    constraints = []
    for blocked in [diane_blocked, jack_blocked, eugene_blocked, patricia_blocked]:
        for i in range(0, len(blocked), 2):
            for start_time in possible_start_times:
                constraints.append(Or(start_time + meeting_duration > blocked[i] + blocked[i+1], 
                                      start_time + meeting_duration < blocked[i]))

    # Solve the constraints
    solver = Solver()
    for start_time in possible_start_times:
        constraints2 = [start_time >= 9 * 60, start_time <= 17 * 60, start_time % 60 == 0]
        for constraint in constraints:
            constraints2.append(constraint)
        solver.add(constraints2)
        if solver.check() == sat:
            model = solver.model()
            start_time_val = model[start_time].as_long()
            return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}\nEnd Time: {(start_time_val // 60 + 1) * 60 + (start_time_val % 60 + meeting_duration) % 60:02d}:{((start_time_val // 60 + 1) * 60 + (start_time_val % 60 + meeting_duration) % 60) % 60:02d}'

    # If no solution is found, try to find a time slot that works for everyone
    for hour in range(9, 17):
        start_time_val = hour * 60
        end_time_val = start_time_val + meeting_duration
        works_for_everyone = True
        for blocked in [diane_blocked, jack_blocked, eugene_blocked, patricia_blocked]:
            for i in range(0, len(blocked), 2):
                if start_time_val < blocked[i] + blocked[i+1] and start_time_val + meeting_duration > blocked[i]:
                    works_for_everyone = False
                    break
            if not works_for_everyone:
                break
        if works_for_everyone:
            return f'SOLUTION:\nDay: {day}\nStart Time: {hour:02d}:{start_time_val % 60:02d}\nEnd Time: {(hour + 1) % 24:02d}:{(end_time_val % 60):02d}'

    return 'No solution found'

# Define the blocked times for each participant
diane_blocked = [9 * 60 + 30, 10 * 60, 14 * 60 + 30, 15 * 60]
jack_blocked = [13 * 60 + 30, 14 * 60, 14 * 60 + 30, 15 * 60]
eugene_blocked = [9 * 60, 10 * 60, 10 * 60 + 30, 11 * 60 + 30, 12 * 60, 14 * 60 + 30, 15 * 60, 16 * 60 + 30]
patricia_blocked = [9 * 60 + 30, 10 * 60 + 30, 11 * 60, 12 * 60, 12 * 60 + 30, 14 * 60, 15 * 60, 16 * 60 + 30]

# Define the meeting duration
meeting_duration = 30

print(schedule_meeting(diane_blocked, jack_blocked, eugene_blocked, patricia_blocked, meeting_duration))