from z3 import *

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a Z3 optimizer
optimizer = Optimize()

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
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Tuesday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Wednesday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Thursday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Friday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))

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
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Tuesday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Wednesday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Thursday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))
        elif day == "Friday":
            optimizer.add(Not(meeting_time[time_index(day, h, m)]))

# Frances would like to avoid more meetings on Tuesday
# We will give preference to other days by adding a soft constraint
# This can be done by adding a penalty for Tuesday slots
penalty = Int('penalty')
optimizer.add(penalty >= 0)

# Add penalty for each Tuesday slot
for (h, m) in time_slots:
    optimizer.add(penalty >= If(meeting_time[time_index("Tuesday", h, m)], 1, 0))

# Ensure that the meeting time is continuous for 30 minutes
for day in days:
    for i in range(len(time_slots) - meeting_duration + 1):
        optimizer.add(Implies(meeting_time[time_index(day, time_slots[i][0], time_slots[i][1])],
                           meeting_time[time_index(day, time_slots[i + meeting_duration - 1][0], time_slots[i + meeting_duration - 1][1])]))

# Ensure that only one meeting time is selected
optimizer.add(AtMost(*meeting_time, 1))
optimizer.add(AtLeast(*meeting_time, 1))

# Minimize the penalty
optimizer.minimize(penalty)

# Solve the problem
if optimizer.check() == sat:
    model = optimizer.model()
    for i in range(len(meeting_time)):
        if model.evaluate(meeting_time[i]):
            day_index = i // len(time_slots)
            time_index = i % len(time_slots)
            start_hour, start_minute = time_slots[time_index]
            end_hour, end_minute = time_slots[time_index + meeting_duration - 1]
            if end_minute == 60:
                end_hour += 1
                end_minute = 0
            print(f"SOLUTION:\nDay: {days[day_index]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")