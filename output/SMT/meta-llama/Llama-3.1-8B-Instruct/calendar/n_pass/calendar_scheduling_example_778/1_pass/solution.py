from z3 import *

# Define the days of the week
days = ['Monday', 'Tuesday', 'Wednesday']

# Define the time slots for each day
time_slots = {
    'Monday': [
        (9, 13),  # 9:00 to 13:00
        (13, 14),  # 13:00 to 14:00
        (14, 16),  # 14:00 to 16:00
        (16, 17)   # 16:00 to 17:00
    ],
    'Tuesday': [
        (9, 9),    # 9:00 to 9:00
        (9, 10),   # 9:00 to 10:00
        (10, 11),  # 10:00 to 11:00
        (11, 12),  # 11:00 to 12:00
        (12, 13),  # 12:00 to 13:00
        (13, 14),  # 13:00 to 14:00
        (14, 16),  # 14:00 to 16:00
        (16, 17)   # 16:00 to 17:00
    ],
    'Wednesday': [
        (9, 10),  # 9:00 to 10:00
        (10, 10),  # 10:00 to 10:00
        (10, 11),  # 10:00 to 11:00
        (11, 12),  # 11:00 to 12:00
        (12, 12),  # 12:00 to 12:00
        (12, 13),  # 12:00 to 13:00
        (13, 14),  # 13:00 to 14:00
        (14, 14),  # 14:00 to 14:00
        (14, 15),  # 14:00 to 15:00
        (15, 16),  # 15:00 to 16:00
        (16, 17)   # 16:00 to 17:00
    ]
}

# Define the schedules for Susan and Sandra
susan_schedule = {
    'Monday': [(12, 13), (13, 14)],
    'Tuesday': [(11, 12)],
    'Wednesday': [(9, 10), (14, 14), (15, 16)]
}
sandra_schedule = {
    'Monday': [(9, 13), (14, 15), (16, 16), (16, 17)],
    'Tuesday': [(9, 9), (10, 12), (12, 13), (14, 14), (16, 17)],
    'Wednesday': [(9, 11), (12, 12), (13, 17)]
}

# Define the preferences
susan_preferences = {
    'Tuesday': True
}
sandra_preferences = {
    'Monday': {'after': (16, 17)}
}

# Create Z3 solver
solver = Solver()

# Declare variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define constraints
for d in days:
    for i in range(len(time_slots[d])):
        if d == 'Monday' and i >= 3:
            continue
        if d == 'Tuesday' and (i == 7 or i == 5):
            continue
        if d == 'Wednesday' and (i == 8 or i == 9):
            continue
        solver.add(Or(start_time == i, start_time!= i))

solver.add(And(9 <= start_time, start_time <= 16))
solver.add(And(start_time + 0.5 <= end_time, end_time <= 17))

solver.add(Implies(day == 0, And(start_time >= 0, start_time <= 3)))
solver.add(Implies(day == 1, And(start_time >= 0, start_time <= 7)))
solver.add(Implies(day == 2, And(start_time >= 0, start_time <= 9)))

for d in days:
    for i in range(len(time_slots[d])):
        if d == 'Monday' and i >= 3:
            continue
        if d == 'Tuesday' and (i == 7 or i == 5):
            continue
        if d == 'Wednesday' and (i == 8 or i == 9):
            continue
        solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= time_slots[d][i][0], start_time < time_slots[d][i][1]))))

for d in days:
    for i in range(len(time_slots[d])):
        if d == 'Monday' and i >= 3:
            continue
        if d == 'Tuesday' and (i == 7 or i == 5):
            continue
        if d == 'Wednesday' and (i == 8 or i == 9):
            continue
        if d == 'Monday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Monday' and i == 3:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Tuesday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 11, start_time < 12))))
        if d == 'Wednesday' and i == 0:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 9, start_time < 10))))
        if d == 'Wednesday' and i == 5:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Wednesday' and i == 6:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Wednesday' and i == 7:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 14, start_time < 15))))
        if d == 'Wednesday' and i == 8:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 15, start_time < 16))))
        if d == 'Wednesday' and i == 9:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 16, start_time < 17))))

for d in days:
    for i in range(len(time_slots[d])):
        if d == 'Monday' and i >= 3:
            continue
        if d == 'Tuesday' and (i == 7 or i == 5):
            continue
        if d == 'Wednesday' and (i == 8 or i == 9):
            continue
        if d == 'Monday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Monday' and i == 3:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Tuesday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 11, start_time < 12))))
        if d == 'Wednesday' and i == 0:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 9, start_time < 10))))
        if d == 'Wednesday' and i == 5:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Wednesday' and i == 6:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Wednesday' and i == 7:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 14, start_time < 15))))
        if d == 'Wednesday' and i == 8:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 15, start_time < 16))))
        if d == 'Wednesday' and i == 9:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 16, start_time < 17))))

for d in days:
    for i in range(len(time_slots[d])):
        if d == 'Monday' and i >= 3:
            continue
        if d == 'Tuesday' and (i == 7 or i == 5):
            continue
        if d == 'Wednesday' and (i == 8 or i == 9):
            continue
        if d == 'Monday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Monday' and i == 3:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Tuesday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 11, start_time < 12))))
        if d == 'Wednesday' and i == 0:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 9, start_time < 10))))
        if d == 'Wednesday' and i == 5:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Wednesday' and i == 6:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Wednesday' and i == 7:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 14, start_time < 15))))
        if d == 'Wednesday' and i == 8:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 15, start_time < 16))))
        if d == 'Wednesday' and i == 9:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 16, start_time < 17))))

for d in days:
    for i in range(len(time_slots[d])):
        if d == 'Monday' and i >= 3:
            continue
        if d == 'Tuesday' and (i == 7 or i == 5):
            continue
        if d == 'Wednesday' and (i == 8 or i == 9):
            continue
        if d == 'Monday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Monday' and i == 3:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Tuesday' and i == 2:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 11, start_time < 12))))
        if d == 'Wednesday' and i == 0:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 9, start_time < 10))))
        if d == 'Wednesday' and i == 5:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 12, start_time < 13))))
        if d == 'Wednesday' and i == 6:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 13, start_time < 14))))
        if d == 'Wednesday' and i == 7:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 14, start_time < 15))))
        if d == 'Wednesday' and i == 8:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 15, start_time < 16))))
        if d == 'Wednesday' and i == 9:
            solver.add(Implies(And(day == d_to_int(d), start_time == i), Not(And(start_time >= 16, start_time < 17))))

# Check if a solution exists
if solver.check() == sat:
    model = solver.model()
    day = model[day].as_long()
    start_time = model[start_time].as_long()
    end_time = model[end_time].as_long()
    print(f"SOLUTION:")
    print(f"Day: {days[day]}")
    print(f"Start Time: {start_time:02d}:00")
    print(f"End Time: {end_time:02d}:30")
else:
    print("No solution exists")

def d_to_int(d):
    if d == 'Monday':
        return 0
    elif d == 'Tuesday':
        return 1
    elif d == 'Wednesday':
        return 2