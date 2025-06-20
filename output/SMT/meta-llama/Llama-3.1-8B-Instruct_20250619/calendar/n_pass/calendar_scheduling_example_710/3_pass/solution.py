from z3 import *

def schedule_meeting(cheryl_schedule, kyle_schedule, meeting_duration, preferred_days=None):
    # Create Z3 variables for the day, start time, and end time
    days = [Int("day") for _ in range(3)]
    for i, day in enumerate(days):
        day = Int("day_" + str(i))
        day = day > 0
        day = day < 3
    start_times = [Int("start_time") for _ in range(3)]
    for i, start_time in enumerate(start_times):
        start_time = Int("start_time_" + str(i))
        start_time = start_time >= 9
        start_time = start_time < 17
    end_times = [Int("end_time") for _ in range(3)]
    for i, end_time in enumerate(end_times):
        end_time = Int("end_time_" + str(i))
        end_time = end_time >= 9
        end_time = end_time < 17
        end_time = end_time == start_times[i] + meeting_duration

    # Define the constraints
    constraints = []
    for i, (start_time, end_time) in enumerate(zip(start_times, end_times)):
        constraints.append(And(start_time, end_time))
        constraints.append(Or(days[i] == 0, Not(And(start_time, start_time < 9.5, days[i] == 0))))  # Cheryl is busy on Monday during 9:00 to 9:30
        constraints.append(Or(days[i] == 0, Not(And(start_time, start_time < 11.5, days[i] == 0))))  # Cheryl is busy on Monday during 11:30 to 13:00
        constraints.append(Or(days[i] == 0, Not(And(start_time, start_time < 15.5, days[i] == 0))))  # Cheryl is busy on Monday during 15:30 to 16:00
        constraints.append(Or(days[i] == 1, Not(And(start_time, start_time < 15, days[i] == 1))))  # Cheryl is busy on Tuesday during 15:00 to 15:30
        constraints.append(Or(days[i] == 0, Not(And(start_time, start_time < 17, days[i] == 0))))  # Kyle is busy on Monday during 9:00 to 17:00
        constraints.append(Or(days[i] == 1, Not(And(start_time, start_time < 17, days[i] == 1))))  # Kyle is busy on Tuesday during 9:30 to 17:00
        constraints.append(Or(days[i] == 2, Not(And(start_time, start_time < 9.5, days[i] == 2))))  # Kyle is busy on Wednesday during 9:00 to 9:30
        constraints.append(Or(days[i] == 2, Not(And(start_time, start_time < 13, days[i] == 2))))  # Kyle is busy on Wednesday during 10:00 to 13:00
        constraints.append(Or(days[i] == 2, Not(And(start_time, start_time < 13.5, days[i] == 2))))  # Kyle is busy on Wednesday during 13:30 to 14:00
        constraints.append(Or(days[i] == 2, Not(And(start_time, start_time < 14.5, days[i] == 2))))  # Kyle is busy on Wednesday during 14:30 to 17:00
        constraints.append(Or(days[i] == 2, Not(start_time == 9)))  # Cheryl can not meet on Wednesday

    # Solve the constraints
    solver = Solver()
    for constraint in constraints:
        solver.add(constraint)
    if solver.check() == sat:
        model = solver.model()
        day = model[days[0]].as_long()
        start_time = model[start_times[0]].as_long()
        end_time = model[end_times[0]].as_long()
        return f"SOLUTION:\nDay: {['Monday', 'Tuesday', 'Wednesday'][day]}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00"
    else:
        return "No solution found"

# Example usage
cheryl_schedule = [9, 9.5, 11.5, 13, 15.5, 16]
kyle_schedule = [9, 17, 9.5, 17, 10, 13, 13.5, 14, 14.5, 17]
meeting_duration = 0.5
print(schedule_meeting(cheryl_schedule, kyle_schedule, meeting_duration))