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
busy_times_megan = [900, 930, 1000, 1030, 1200, 1230]
for time in busy_times_megan:
    solver.add(vars[("Megan", time)])

# Christine is busy on 9:00-9:30, 11:30-12:00, 13:00-14:00, 15:30-16:30
busy_times_christine = [900, 930, 1130, 1200, 1300, 1330, 1530, 1600]
for time in busy_times_christine:
    solver.add(vars[("Christine", time)])

# Gabriel is free the entire day (no constraints needed)

# Sara is busy on 11:30-12:00, 14:30-15:00
busy_times_sara = [1130, 1200, 1430, 1500]
for time in busy_times_sara:
    solver.add(vars[("Sara", time)])

# Bruce is busy on 9:30-10:00, 10:30-12:00, 12:30-14:00, 14:30-15:00, 15:30-16:30
busy_times_bruce = [930, 1000, 1030, 1100, 1230, 1300, 1430, 1500, 1530, 1600]
for time in busy_times_bruce:
    solver.add(vars[("Bruce", time)])

# Kathryn is busy on 10:00-15:30, 16:00-16:30
busy_times_kathryn = list(range(1000, 1530 + 1, 30)) + [1600, 1630]
for time in busy_times_kathryn:
    solver.add(vars[("Kathryn", time)])

# Billy is busy on 9:00-9:30, 11:00-11:30, 12:00-14:00, 14:30-15:30
busy_times_billy = [900, 930, 1100, 1130] + list(range(1200, 1400 + 1, 30)) + [1430, 1500]
for time in busy_times_billy:
    solver.add(vars[("Billy", time)])

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