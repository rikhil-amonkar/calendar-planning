from z3 import *

def solve_meeting_scheduling():
    # Define the variables
    day = [Bool('day_{}'.format(i)) for i in range(3)]
    start_time = [Int('start_time_{}'.format(i)) for i in range(3)]
    end_time = [Int('end_time_{}'.format(i)) for i in range(3)]

    # Define the constraints
    martha_blocked = [
        Or(day[0], start_time[0] >= 16, start_time[0] < 17),
        Or(day[1], start_time[1] >= 15, start_time[1] < 15.5),
        Or(day[2], start_time[2] >= 10, start_time[2] < 11),
        Or(day[2], start_time[2] >= 14, start_time[2] < 14.5)
    ]
    beverly_blocked = [
        Or(day[0], start_time[0] >= 9, start_time[0] < 13.5),
        Or(day[0], start_time[0] >= 14, start_time[0] < 17),
        Or(day[1], start_time[1] >= 9, start_time[1] < 17),
        Or(day[2], start_time[2] >= 9.5, start_time[2] < 15.5),
        Or(day[2], start_time[2] >= 16.5, start_time[2] < 17)
    ]
    meeting_duration = [start_time[i] + 1 == end_time[i] for i in range(3)]

    # Define the objective function
    objective = And(
        And(day[0], start_time[0] >= 9, start_time[0] < 17),
        And(day[1], start_time[1] >= 9, start_time[1] < 17),
        And(day[2], start_time[2] >= 9, start_time[2] < 17),
        And(martha_blocked, beverly_blocked, meeting_duration)
    )

    # Solve the problem
    s = Solver()
    s.add(objective)
    s.add(Or(day[0], day[1], day[2]))
    s.add(Or(start_time[0] >= 9, start_time[0] < 17, start_time[0] >= 17))
    s.add(Or(start_time[1] >= 9, start_time[1] < 17, start_time[1] >= 17))
    s.add(Or(start_time[2] >= 9, start_time[2] < 17, start_time[2] >= 17))
    s.add(Or(end_time[0] >= 9, end_time[0] < 17, end_time[0] >= 17))
    s.add(Or(end_time[1] >= 9, end_time[1] < 17, end_time[1] >= 17))
    s.add(Or(end_time[2] >= 9, end_time[2] < 17, end_time[2] >= 17))

    if s.check() == sat:
        model = s.model()
        day_to_meet = 'Monday' if model[day[0]] else 'Tuesday' if model[day[1]] else 'Wednesday'
        start_time_to_meet = model[start_time[0]] if model[day[0]] else model[start_time[1]] if model[day[1]] else model[start_time[2]]
        end_time_to_meet = model[end_time[0]] if model[day[0]] else model[end_time[1]] if model[day[1]] else model[end_time[2]]
        return 'SOLUTION:\nDay: {}\nStart Time: {:02d}:{:02d}\nEnd Time: {:02d}:{:02d}'.format(
            day_to_meet, start_time_to_meet.as_integer(), int((start_time_to_meet.as_integer() % 1) * 60),
            end_time_to_meet.as_integer(), int((end_time_to_meet.as_integer() % 1) * 60))
    else:
        return 'No solution found'

print(solve_meeting_scheduling())