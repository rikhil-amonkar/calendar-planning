from z3 import *

def schedule_meeting(day, start_time, end_time, constraints):
    # Define the variables
    times = [Int(f"t_{i}") for i in range(96)]  # 96 possible time slots
    attendees = [Bool(f"att_{i}") for i in range(6)]  # 6 attendees

    # Define the constraints
    for i in range(96):
        t = times[i]
        constraints.append(t >= start_time * 60 + i)
        constraints.append(t <= end_time * 60 + i)

    for i in range(6):
        constraints.append(attendees[i] >= Or([times[j] >= start_time * 60 + i * 30 for j in range(96)]))
        constraints.append(attendees[i] >= Or([times[j] <= end_time * 60 + i * 30 for j in range(96)]))

    for i in range(6):
        for j in range(96):
            t = times[j]
            constraints.append(And(attendees[i], t < start_time * 60 + (i + 1) * 30) == False)
            constraints.append(And(attendees[i], t >= end_time * 60 + i * 30) == False)

    for attendee in range(6):
        constraints.append(Or(attendees[attendee], Not(attendees[attendee])))

    for attendee in range(6):
        for time in range(96):
            t = times[time]
            constraints.append(And(attendees[attendee], t >= start_time * 60 + attendee * 30, t <= end_time * 60 + attendee * 30) == False)

    for attendee, schedule in enumerate(constraints[6:]):
        for time in range(96):
            t = times[time]
            constraints.append(And(attendees[attendee], t >= schedule[0], t <= schedule[1]) == False)

    # Solve the constraints
    solver = Solver()
    for constraint in constraints:
        solver.add(constraint)
    if solver.check() == sat:
        model = solver.model()
        start_time = 9
        for time in range(96):
            if model.eval(times[time]) == 1:
                break
        end_time = (time // 2) + 9
        return f"SOLUTION: Day: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:30"
    else:
        return "No solution found"

# Define the existing schedules and preferences
schedules = {
    "Jose": [(11, 11.5), (12.5, 13)],
    "Keith": [(14, 14.5), (15, 15.5)],
    "Logan": [(9, 10), (12, 12.5), (15, 15.5)],
    "Megan": [(9, 10.5), (11, 12), (13, 13.5), (14.5, 16.5)],
    "Gary": [(9, 9.5), (10, 10.5), (11.5, 13), (13.5, 14), (14.5, 16.5)],
    "Bobby": [(11, 11.5), (12, 12.5), (13, 16)]
}

# Define the preferences
preferences = {
    "Jose": "No meeting after 15:30"
}

# Find a time that works for everyone's schedule and constraints
day = "Monday"
start_time = 9
end_time = 17
meeting_duration = 0.5
constraints = []
for attendee, schedule in schedules.items():
    for start, end in schedule:
        constraints.append((start, end))
for attendee, preference in preferences.items():
    if preference == "No meeting after 15:30":
        constraints.append((15.5, 17))

print(schedule_meeting(day, start_time, end_time, constraints))