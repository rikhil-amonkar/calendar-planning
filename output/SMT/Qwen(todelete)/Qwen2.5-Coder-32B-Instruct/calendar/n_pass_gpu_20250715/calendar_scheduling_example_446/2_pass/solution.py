from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900 + i * 30 for i in range(0, 16)]  # 900 represents 9:00, 930 represents 9:30, ..., 1630 represents 16:30

# Create a boolean variable for each person and each time slot
vars = {}
for person in ["Megan", "Christine", "Gabriel", "Sara", "Bruce", "Kathryn", "Billy"]:
    for time in time_slots:
        vars[(person, time)] = Bool(f"{person}_{time}")

# Create a solver instance
solver = Solver()

# Add constraints based on the existing schedules
# Megan is busy on 9:00-9:30, 10:00-11:00, 12:00-12:30
solver.add(And(vars[("Megan", 900)], vars[("Megan", 930)]))
solver.add(And(vars[("Megan", 1000)], vars[("Megan", 1030)]))
solver.add(And(vars[("Megan", 1200)], vars[("Megan", 1230)]))

# Christine is busy on 9:00-9:30, 11:30-12:00, 13:00-14:00, 15:30-16:30
solver.add(And(vars[("Christine", 900)], vars[("Christine", 930)]))
solver.add(And(vars[("Christine", 1130)], vars[("Christine", 1200)]))
solver.add(And(vars[("Christine", 1300)], vars[("Christine", 1330)]))
solver.add(And(vars[("Christine", 1530)], vars[("Christine", 1600)]))

# Gabriel is free the entire day (no constraints needed)

# Sara is busy on 11:30-12:00, 14:30-15:00
solver.add(And(vars[("Sara", 1130)], vars[("Sara", 1200)]))
solver.add(And(vars[("Sara", 1430)], vars[("Sara", 1500)]))

# Bruce is busy on 9:30-10:00, 10:30-12:00, 12:30-14:00, 14:30-15:00, 15:30-16:30
solver.add(And(vars[("Bruce", 930)], vars[("Bruce", 1000)]))
solver.add(And(vars[("Bruce", 1030)], vars[("Bruce", 1100)]))
solver.add(And(vars[("Bruce", 1230)], vars[("Bruce", 1300)]))
solver.add(And(vars[("Bruce", 1430)], vars[("Bruce", 1500)]))
solver.add(And(vars[("Bruce", 1530)], vars[("Bruce", 1600)]))

# Kathryn is busy on 10:00-15:30, 16:00-16:30
for t in range(1000, 1530 + 1, 30):
    solver.add(vars[("Kathryn", t)])
solver.add(vars[("Kathryn", 1600)])
solver.add(vars[("Kathryn", 1630)])

# Billy is busy on 9:00-9:30, 11:00-11:30, 12:00-14:00, 14:30-15:30
solver.add(And(vars[("Billy", 900)], vars[("Billy", 930)]))
solver.add(And(vars[("Billy", 1100)], vars[("Billy", 1130)]))
for t in range(1200, 1400 + 1, 30):
    solver.add(vars[("Billy", t)])
solver.add(And(vars[("Billy", 1430)], vars[("Billy", 1500)]))

# Ensure that all participants are free for a 30-minute slot
meeting_time = Int('meeting_time')
solver.add(meeting_time >= 900)
solver.add(meeting_time <= 1630)
solver.add(meeting_time % 30 == 0)

# All participants must be free at the meeting time
for person in ["Megan", "Christine", "Gabriel", "Sara", "Bruce", "Kathryn", "Billy"]:
    solver.add(Not(vars[(person, meeting_time)]))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[meeting_time].as_long()
    meeting_end = meeting_start + 30
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start // 100}:{meeting_start % 100:02}\nEnd Time: {meeting_end // 100}:{meeting_end % 100:02}")
else:
    print("No solution found")