from z3 import *

def solve_meeting_schedule(carl_schedule, margaret_schedule, preferred_day, meeting_duration):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Define the start and end times
    start_time = 9
    end_time = 17
    time_slots = [Int(f"slot_{i}") for i in range(4 * (end_time - start_time))]

    # Define the constraints for Carl's schedule
    carl_constraints = []
    for i in range(len(carl_schedule)):
        day = days.index(carl_schedule[i][0])
        start = carl_schedule[i][1]
        end = carl_schedule[i][2]
        for j in range(start * 4, end * 4):
            carl_constraints.append(Not(time_slots[j]))

    # Define the constraints for Margaret's schedule
    margaret_constraints = []
    for i in range(len(margaret_schedule)):
        day = days.index(margaret_schedule[i][0])
        start = margaret_schedule[i][1]
        end = margaret_schedule[i][2]
        for j in range(start * 4, end * 4):
            margaret_constraints.append(Not(time_slots[j]))

    # Define the constraint to avoid more meetings on Thursday for Carl
    if preferred_day == 'Thursday':
        carl_constraints.append(Not(time_slots[16]))

    # Define the constraint for the meeting duration
    for i in range(len(time_slots) - 1):
        time_slots[i] = time_slots[i] + 1
        time_slots[i] = If(time_slots[i] > 16, 0, time_slots[i])
        time_slots[i+1] = time_slots[i+1] + 1
        time_slots[i+1] = If(time_slots[i+1] > 16, 0, time_slots[i+1])
        time_slots[i] = time_slots[i] * 30 + time_slots[i+1]
        time_slots[i+1] = 0
    for i in range(len(time_slots) - 1):
        time_slots[i] = If(time_slots[i] > 480, 0, time_slots[i])
    time_slots = [Bool(f"time_{i}") for i in range(len(time_slots))]

    # Define the constraints for the meeting time
    for i in range(len(time_slots) - meeting_duration + 1):
        time_slots[i] = time_slots[i] + meeting_duration
        time_slots[i] = If(time_slots[i] > len(time_slots) - 1, 0, time_slots[i])

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    for constraint in carl_constraints:
        solver.add(constraint)
    for constraint in margaret_constraints:
        solver.add(constraint)

    # Add the constraints for the meeting time
    for i in range(len(time_slots) - meeting_duration + 1):
        solver.add(Or([time_slots[i], time_slots[i+1], time_slots[i+2], time_slots[i+3]]))

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day = days[model[time_slots[0]].as_long() // 4]
        start_time = model[time_slots[0]].as_long() % 4
        end_time = model[time_slots[1]].as_long() % 4
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00"
    else:
        return "No solution found"

# Example usage
carl_schedule = [('Monday', 11, 11), ('Tuesday', 14, 15), ('Wednesday', 10, 11), ('Wednesday', 13, 13), ('Thursday', 13, 14), ('Thursday', 16, 16)]
margaret_schedule = [('Monday', 9, 10), ('Monday', 11, 17), ('Tuesday', 9, 12), ('Tuesday', 13, 14), ('Tuesday', 15, 17), ('Wednesday', 9, 12), ('Wednesday', 12, 13), ('Wednesday', 13, 14), ('Wednesday', 15, 17), ('Thursday', 10, 12), ('Thursday', 12, 14), ('Thursday', 14, 17)]
preferred_day = 'Wednesday'
meeting_duration = 60

print(solve_meeting_schedule(carl_schedule, margaret_schedule, preferred_day, meeting_duration))