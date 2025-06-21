from z3 import *

def schedule_meeting(schedules, duration):
    # Define the variables
    day = [Bool('day_' + str(i)) for i in range(1, 8)]  # Monday to Sunday
    start_time = [Int('start_time_' + str(i)) for i in range(1, 7)]  # 9:00 to 16:00
    end_time = [start_time[i] + duration for i in range(7)]

    # Add constraints
    constraints = []
    for i in range(7):
        constraints.append(And(day[i], start_time[i] >= 9, start_time[i] <= 16))
        constraints.append(And(day[i], end_time[i] >= 9, end_time[i] <= 16))

    for person, schedule in schedules.items():
        for time in schedule:
            start, end = time
            constraints.append(Not(And(day[0], And(start_time[0] >= start, start_time[0] <= end))))
            constraints.append(Not(And(day[0], And(end_time[0] >= start, end_time[0] <= end))))

    # Solve the constraints
    solver = Solver()
    for constraint in constraints:
        solver.add(constraint)
    solver.add(Or(day))

    if solver.check() == sat:
        model = solver.model()
        day_to_meet = [i for i, b in enumerate(model[day]) if b][0]
        start_time_to_meet = model[start_time[day_to_meet]].as_long()
        end_time_to_meet = model[end_time[day_to_meet]].as_long()

        return f"SOLUTION:\nDay: Monday\nStart Time: {start_time_to_meet:02d}:00\nEnd Time: {end_time_to_meet:02d}:00"
    else:
        return "No solution found"

schedules = {
    'Christine': [(11, 11.5), (15, 15.5)],
    'Helen': [(9.5, 10.5), (11, 11.5), (12, 12.5), (13.5, 15.5), (16.5, 17)]
}
duration = 0.5

print(schedule_meeting(schedules, duration))