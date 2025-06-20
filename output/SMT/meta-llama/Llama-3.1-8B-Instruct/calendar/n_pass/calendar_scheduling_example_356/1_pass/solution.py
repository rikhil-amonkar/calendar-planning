from z3 import *

def schedule_meeting(day, start_time, end_time, schedules, preferences):
    # Define the Z3 solver
    s = Solver()

    # Define the variables
    meeting_time = [Bool(f'meeting_time_{i}') for i in range(len(schedules))]

    # Add constraints for each participant
    for i, (schedule, preference) in enumerate(zip(schedules, preferences)):
        for t in schedule:
            s.add(Not(meeting_time[i]))
        if preference:
            s.add(Or([meeting_time[i] for i in range(len(schedules))]))

    # Add constraints for the meeting time
    s.add(And([meeting_time[i] for i in range(len(schedules))]))
    s.add(And([start_time <= end_time]))
    s.add(And([start_time >= 9 * 60]))
    s.add(And([end_time <= 17 * 60]))
    s.add(And([end_time - start_time == 30]))

    # Add constraints for the day
    s.add(And([start_time >= 9 * 60 + 30 if i == 0 else start_time >= schedules[i][0][0] for i in range(len(schedules))]))
    s.add(And([end_time <= 17 * 60 - 30 if i == 0 else end_time <= schedules[i][-1][1] for i in range(len(schedules))]))

    # Check the solution
    if s.check() == sat:
        model = s.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}'
    else:
        return 'No solution found'

# Define the schedules and preferences
schedules = [
    [(12 * 60, 12 * 60 + 30), (13 * 60, 14 * 60 + 30)],
    [],
    [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],
    [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
    [(9 * 60, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    [(9 * 60, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
]
preferences = [False, False, False, True, False, False]

# Call the function
print(schedule_meeting('Monday','start_time', 'end_time', schedules, preferences))