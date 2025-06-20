from z3 import *

def solve_meeting(shirley_schedule, albert_schedule, meeting_duration, preferred_day=None):
    # Create Z3 variables
    day = [Bool('day_' + str(i)) for i in range(2)]
    start_time = [Int('start_time_' + str(i)) for i in range(2)]
    end_time = [Int('end_time_' + str(i)) for i in range(2)]

    # Define constraints
    for i in range(2):
        start_time[i] = IntVal(9 * 60) + If(day[i], IntVal(0), IntVal(1) * 60)
        end_time[i] = start_time[i] + meeting_duration

    # Shirley's constraints
    for i in range(2):
        for time in shirley_schedule[i]:
            start, end = time
            start, end = IntVal(start * 60), IntVal(end * 60)
            if i == 0:
                # Monday
                start_time[i] >= start
                end_time[i] <= end
            else:
                # Tuesday
                start_time[i] >= start
                end_time[i] <= end
                if end_time[i] > 10 * 60:
                    day[i] = False

    # Albert's constraints
    for i in range(2):
        for time in albert_schedule[i]:
            start, end = time
            start, end = IntVal(start * 60), IntVal(end * 60)
            if i == 0:
                # Monday
                start_time[i] >= start
                end_time[i] <= end
            else:
                # Tuesday
                start_time[i] >= start
                end_time[i] <= end
                if end_time[i] > 9 * 60 or end_time[i] < 11 * 60 or end_time[i] > 13 * 60 or end_time[i] < 16 * 60 or end_time[i] > 16 * 60 + 30:
                    day[i] = False

    # Meeting duration constraint
    for i in range(2):
        if day[i]:
            start_time[i] + meeting_duration - 1 >= end_time[i]

    # Preferred day constraint
    if preferred_day is not None:
        day[preferred_day] = True

    # Solve the problem
    solver = Solver()
    solver.add(Or(day[0], day[1]))
    solver.add(And(start_time[0] < end_time[0], start_time[1] < end_time[1]))
    solver.add(And(9 * 60 <= start_time[0], start_time[0] <= 17 * 60, 9 * 60 <= start_time[1], start_time[1] <= 17 * 60))
    solver.add(And(9 * 60 <= end_time[0], end_time[0] <= 17 * 60, 9 * 60 <= end_time[1], end_time[1] <= 17 * 60))
    if solver.check() == sat:
        model = solver.model()
        day_idx = [model.evaluate(day[i]).as_bool().value() for i in range(2)].index(True)
        return f'Day: {["Monday", "Tuesday"][day_idx]}\nStart Time: {str(model.evaluate(start_time[day_idx] // 60)).zfill(2) + ":" + str(model.evaluate(start_time[day_idx] % 60)).zfill(2)}\nEnd Time: {str(model.evaluate(end_time[day_idx] // 60)).zfill(2) + ":" + str(model.evaluate(end_time[day_idx] % 60)).zfill(2)}'
    else:
        return 'No solution found'

shirley_schedule = [[(10.5, 11.0), (12.0, 12.3), (16.0, 16.3)], [(9.5, 10.0)]]
albert_schedule = [[(9.0, 17.0)], [(9.5, 11.0), (11.3, 12.3), (13.0, 16.0), (16.3, 17.0)]]
meeting_duration = 30
preferred_day = 0

print(solve_meeting(shirley_schedule, albert_schedule, meeting_duration, preferred_day))