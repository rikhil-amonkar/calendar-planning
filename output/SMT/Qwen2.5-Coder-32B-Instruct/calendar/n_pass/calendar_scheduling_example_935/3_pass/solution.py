from z3 import *

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a Z3 solver
solver = Solver()

# Define a Boolean variable for each possible meeting time and day
meeting_time = BoolVector('meeting_time', len(days) * len(time_slots))

# Helper function to convert day and time to index
def time_index(day, hour, minute):
    return days.index(day) * len(time_slots) + time_slots.index((hour, minute))

# Define the meeting duration (30 minutes)
meeting_duration = 1

# Define the constraints for Terry's availability
terry_busy = [
    (10, 30), (12, 30), (15, 0),  # Monday
    (9, 30), (10, 30), (14, 0), (16, 0),  # Tuesday
    (9, 30), (11, 0), (13, 0), (15, 0), (16, 30),  # Wednesday
    (9, 30), (12, 0), (13, 0), (16, 0),  # Thursday
    (9, 0), (12, 0), (13, 30), (16, 30)  # Friday
]

for day in days:
    for (h, m) in terry_busy:
        if day == "Monday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Tuesday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Wednesday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Thursday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Friday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))

# Define the constraints for Frances's availability
frances_busy = [
    (9, 30), (11, 30), (14, 0), (15, 0),  # Monday
    (9, 0), (10, 0), (11, 0), (13, 0), (15, 30),  # Tuesday
    (9, 30), (10, 30), (11, 30), (16, 0),  # Wednesday
    (11, 0), (14, 30),  # Thursday
    (9, 30), (11, 0), (13, 0), (16, 0)  # Friday
]

for day in days:
    for (h, m) in frances_busy:
        if day == "Monday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Tuesday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Wednesday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Thursday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Friday":
            solver.add(Not(meeting_time[time_index(day, h, m)]))

# Ensure that the meeting time is within the work hours and does not overlap
for day in days:
    for i in range(len(time_slots) - meeting_duration + 1):
        solver.add(Implies(meeting_time[time_index(day, time_slots[i][0], time_slots[i][1])],
                           And([Not(meeting_time[time_index(day, time_slots[i + j][0], time_slots[i + j][1])])
                                for j in range(1, meeting_duration)])))

# Find the earliest available time
for day in days:
    for (h, m) in time_slots:
        if solver.check() == sat:
            model = solver.model()
            if model.evaluate(meeting_time[time_index(day, h, m)]):
                end_h = h + (m + 30) // 60
                end_m = (m + 30) % 60
                print(f"SOLUTION:\nDay: {day}\nStart Time: {h:02}:{m:02}\nEnd Time: {end_h:02}:{end_m:02}")
                break
    else:
        continue
    break

# If no solution is found, print an error message
if solver.check() != sat:
    print("No solution found")