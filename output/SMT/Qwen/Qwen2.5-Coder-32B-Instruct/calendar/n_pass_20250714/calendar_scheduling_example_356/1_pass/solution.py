from z3 import *

# Define the solver
solver = Solver()

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a boolean variable for each time slot indicating if the meeting is scheduled at that time
meeting_time_vars = {(h, m): Bool(f"meeting_at_{h}_{m}") for h, m in time_slots}

# Add constraints for each person's availability
# Katherine is busy on Monday during 12:00 to 12:30, 13:00 to 14:30
for h, m in time_slots:
    if (h == 12 and m == 0) or (h == 12 and m == 30) or (h == 13 and m == 0) or (h == 13 and m == 30) or (h == 14 and m == 0):
        solver.add(Not(meeting_time_vars[(h, m)]))

# Rebecca has no meetings the whole day
# No additional constraints needed for Rebecca

# Julie is busy on Monday during 9:00 to 9:30, 10:30 to 11:00, 13:30 to 14:00, 15:00 to 15:30
for h, m in time_slots:
    if (h == 9 and m == 0) or (h == 9 and m == 30) or (h == 10 and m == 30) or (h == 13 and m == 30) or (h == 15 and m == 0):
        solver.add(Not(meeting_time_vars[(h, m)]))

# Angela has meetings on Monday during 9:00 to 10:00, 10:30 to 11:00, 11:30 to 14:00, 14:30 to 15:00, 16:30 to 17:00
# Angela would like to avoid more meetings on Monday before 15:00
for h, m in time_slots:
    if (h == 9 and m == 0) or (h == 9 and m == 30) or (h == 10 and m == 30) or (h == 11 and m == 30) or (h == 11 and m == 0) or \
       (h == 12 and m == 0) or (h == 12 and m == 30) or (h == 13 and m == 0) or (h == 13 and m == 30) or (h == 14 and m == 0) or \
       (h == 14 and m == 30) or (h == 15 and m == 0) or (h == 16 and m == 30):
        solver.add(Not(meeting_time_vars[(h, m)]))

# Nicholas has blocked their calendar on Monday during 9:30 to 11:00, 11:30 to 13:30, 14:00 to 16:00, 16:30 to 17:00
for h, m in time_slots:
    if (h == 9 and m == 30) or (h == 10 and m == 0) or (h == 10 and m == 30) or (h == 11 and m == 0) or (h == 11 and m == 30) or \
       (h == 12 and m == 0) or (h == 12 and m == 30) or (h == 13 and m == 0) or (h == 13 and m == 30) or (h == 14 and m == 0) or \
       (h == 14 and m == 30) or (h == 15 and m == 0) or (h == 15 and m == 30) or (h == 16 and m == 0) or (h == 16 and m == 30):
        solver.add(Not(meeting_time_vars[(h, m)]))

# Carl has blocked their calendar on Monday during 9:00 to 11:00, 11:30 to 12:30, 13:00 to 14:30, 15:00 to 16:00, 16:30 to 17:00
for h, m in time_slots:
    if (h == 9 and m == 0) or (h == 9 and m == 30) or (h == 10 and m == 0) or (h == 10 and m == 30) or (h == 11 and m == 0) or \
       (h == 11 and m == 30) or (h == 12 and m == 0) or (h == 12 and m == 30) or (h == 13 and m == 0) or (h == 13 and m == 30) or \
       (h == 14 and m == 0) or (h == 15 and m == 0) or (h == 15 and m == 30) or (h == 16 and m == 0) or (h == 16 and m == 30):
        solver.add(Not(meeting_time_vars[(h, m)]))

# Ensure exactly one time slot is chosen for the meeting
solver.add(Or([meeting_time_vars[ts] for ts in time_slots]))
solver.add(And([Not(And(meeting_time_vars[t1], meeting_time_vars[t2])) for t1 in time_slots for t2 in time_slots if t1 != t2]))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    for ts in time_slots:
        if model.evaluate(meeting_time_vars[ts]):
            h, m = ts
            start_time = f"{h:02}:{m:02}"
            end_time = f"{h+1:02}:{m:02}" if m == 0 else f"{h:02}:{m+30:02}"
            print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")