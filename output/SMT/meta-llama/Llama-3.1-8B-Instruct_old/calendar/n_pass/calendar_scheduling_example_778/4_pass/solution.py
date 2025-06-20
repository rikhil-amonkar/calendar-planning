from z3 import *

def solve_meeting(susan_schedule, sandra_schedule, duration, preferred_day=None):
    # Define the days and time slots
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_time = 9 * 60
    end_time = 17 * 60
    time_slots = [(i, j) for i in range(start_time, end_time) for j in range(i + 30, end_time, 30)]

    # Create Z3 variables
    day = Int('day')
    start = Int('start')
    end = Int('end')

    # Define the constraints
    constraints = [day >= 0, day < len(days), start >= start_time, start < end_time, end >= start, end <= end_time]

    # Add constraints for each person's schedule
    for i, slot in enumerate(time_slots):
        for person in [susan_schedule, sandra_schedule]:
            if slot in person:
                constraints.append(Or(And(day == 0, start!= slot[0]),  # Monday
                                       And(day == 1, start!= slot[0]),  # Tuesday
                                       And(day == 2, start!= slot[0])))  # Wednesday

    # Add constraints for preferred day
    if preferred_day is not None:
        preferred_day_index = days.index(preferred_day)
        constraints.append(day == preferred_day_index)

    # Add constraints for duration
    constraints.append(end - start == 30)  # 30 minutes for half an hour
    constraints.append(Or(And(start >= 9 * 60 + 30, start < 17 * 60),  # within work hours
                          And(day == 0, start < 16 * 60),  # Monday before 16:00
                          And(day == 2, start < 9 * 60)))  # Wednesday before 9:00

    # Add constraints for unavailable time slots on Wednesday
    for i, slot in enumerate(time_slots):
        if (day == 2 and (slot[0] >= 9 * 60 + 30 or slot[1] <= 10 * 60)):
            constraints.append(Not(And(day == 2, start >= 9 * 60, start < 10 * 60)))

    # Add constraints for Sandra's schedule on Monday
    for i, slot in enumerate(time_slots):
        if (day == 0 and start >= 16 * 60) or slot in sandra_schedule:
            constraints.append(Not(And(day == 0, start >= 9 * 60, start < 17 * 60)))

    # Create the solver and solve the problem
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        return f"SOLUTION:\nDay: {days[model[day].as_long()]}\nStart Time: {model[start].as_long() // 60:02d}:{model[start].as_long() % 60:02d}\nEnd Time: {model[end].as_long() // 60:02d}:{model[end].as_long() % 60:02d}"
    else:
        return "No solution found"

# Define the schedules
susan_schedule = [(12 * 60 + 30, 13 * 60), (13 * 60, 14 * 60), (11 * 60 + 30, 12 * 60), (9 * 60 + 30, 10 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60)]
sandra_schedule = [(9 * 60, 13 * 60), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30), (9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60), (9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)]

# Solve the problem
duration = 0.5  # half an hour
print(solve_meeting(susan_schedule, sandra_schedule, duration))