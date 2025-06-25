from z3 import *

def solve_scheduling_problem():
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end time of the work hours
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 30 * 60  # 30 minutes

    # Define the constraints for each participant
    shirley = [10 * 60, 11 * 60, 12 * 60]  # 10:30, 11:00, 12:00
    jacob = [9 * 60, 10 * 60, 11 * 60, 12 * 60 + 30, 14 * 60 + 30]
    stephen = [11 * 60, 12 * 60]
    margaret = [9 * 60, 10 * 60 + 30, 12 * 60, 13 * 60, 15 * 60, 16 * 60 + 30]
    mason = [9 * 60, 10 * 60 + 30, 11 * 60 + 30, 12 * 60, 13 * 60, 14 * 60, 16 * 60 + 30]

    # Margaret's preference
    margaret_preferred_start = 14 * 60

    # Create a Z3 solver
    s = Solver()

    # Define the variables for the start time of the meeting
    start = [Int(f'start_{i}') for i in range(7)]

    # Add constraints for each participant
    for i in range(7):
        s.add(start[i] >= start_time)
        s.add(start[i] <= end_time - meeting_duration)

    for i in range(7):
        for time in [9 * 60, 10 * 60, 11 * 60, 12 * 60, 13 * 60, 14 * 60, 15 * 60, 16 * 60]:
            s.add(Or([start[i] + meeting_duration <= time, start[i] + meeting_duration > time]))

    s.add(Or([start[i]!= 9 * 60 for i in range(7)]))  # Margaret does not want to meet before 14:30
    s.add(Or([start[i]!= 10 * 60 for i in range(7)]))  # Margaret does not want to meet before 14:30
    s.add(Or([start[i]!= 11 * 60 for i in range(7)]))  # Margaret does not want to meet before 14:30
    s.add(Or([start[i]!= 12 * 60 for i in range(7)]))  # Margaret does not want to meet before 14:30

    s.add(And([start[i] + meeting_duration >= time for i, time in enumerate(shirley)]))
    s.add(And([start[i] + meeting_duration >= time for i, time in enumerate(jacob)]))
    s.add(And([start[i] + meeting_duration >= time for i, time in enumerate(stephen)]))
    s.add(And([start[i] + meeting_duration >= time for i, time in enumerate(margaret)]))
    s.add(And([start[i] + meeting_duration >= time for i, time in enumerate(mason)]))

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        start_time = model[start[0]].as_long()
        end_time = start_time + meeting_duration
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time // 60:02d}:{start_time % 60:02d}\nEnd Time: {end_time // 60:02d}:{end_time % 60:02d}'
    else:
        return 'No solution found'

print(solve_scheduling_problem())