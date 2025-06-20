from z3 import *

def solve_meeting_schedule():
    # Define the variables
    day = [Bool('day_' + str(i)) for i in range(3)]
    start_time = [Int('start_' + str(i)) for i in range(3)]
    end_time = [Int('end_' + str(i)) for i in range(3)]

    # Define the constraints
    # Day constraints
    constraints = []
    for i in range(3):
        constraints.append(Or(day[i], day[i] == False))
        constraints.append(Implies(day[i], And(9 <= start_time[i], start_time[i] <= 17)))
        constraints.append(Implies(day[i], And(start_time[i] + 30 <= end_time[i])))

    # Tyler's constraints
    constraints.append(Not(And(day[1], And(9 <= start_time[1], start_time[1] <= 9.5, 14.5 <= end_time[1], end_time[1] <= 15))))
    constraints.append(Not(And(day[2], Or(And(10.5 <= start_time[2], start_time[2] <= 11, 12.5 <= end_time[2], end_time[2] <= 13), 
                                        And(13.5 <= start_time[2], start_time[2] <= 14, 16.5 <= end_time[2], end_time[2] <= 17)))))
    constraints.append(Not(And(day[0], And(9 <= start_time[0], start_time[0] <= 15.5))))

    # Ruth's constraints
    constraints.append(Not(And(day[0], Or(And(9 <= start_time[0], start_time[0] <= 10, 10.5 <= end_time[0], end_time[0] <= 12), 
                                        And(12.5 <= start_time[0], start_time[0] <= 14.5, 15 <= end_time[0], end_time[0] <= 16), 
                                        And(16 <= start_time[0], start_time[0] <= 17, 0 <= end_time[0], end_time[0] <= 17)))))
    constraints.append(Not(And(day[1], 0 <= start_time[1] and end_time[1] <= 17)))
    constraints.append(Not(And(day[2], 0 <= start_time[2] and end_time[2] <= 17)))

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    solver.add(And(day[0], day[1], day[2]))
    if solver.check() == sat:
        model = solver.model()
        day_to_meet = [int(model.evaluate(day[i]).as_long()) for i in range(3)]
        start_time_to_meet = [model.evaluate(start_time[i]).as_long() for i in range(3)]
        end_time_to_meet = [model.evaluate(end_time[i]).as_long() for i in range(3)]

        # Find the first day that has a valid meeting time
        for i in range(3):
            if day_to_meet[i]:
                return f"SOLUTION:\nDay: {['Monday', 'Tuesday', 'Wednesday'][i]}\nStart Time: {str(int(start_time_to_meet[i])).zfill(2) + ':00'}\nEnd Time: {str(int(end_time_to_meet[i])).zfill(2) + ':00'}"
    else:
        return "No solution found"

print(solve_meeting_schedule())