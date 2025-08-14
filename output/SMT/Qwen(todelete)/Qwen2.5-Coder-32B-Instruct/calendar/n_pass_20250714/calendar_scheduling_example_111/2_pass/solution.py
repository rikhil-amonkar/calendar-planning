from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = list(range(16))  # 9:00, 9:30, ..., 16:30

# Create a Z3 solver instance
solver = Solver()

# Define boolean variables for each time slot for each person
gregory = [Bool(f'gregory_{i}') for i in time_slots]
natalie = [Bool(f'natalie_{i}') for i in time_slots]
christine = [Bool(f'christine_{i}') for i in time_slots]
vincent = [Bool(f'vincent_{i}') for i in time_slots]

# Constraints for Gregory
blocked_gregory = [0, 1, 4, 5, 8, 9, 12, 13]  # 9:00-10:00, 10:30-11:30, 12:30-13:00, 13:30-14:00
for i in time_slots:
    if i in blocked_gregory:
        solver.add(gregory[i] == False)

# Constraints for Natalie (no constraints, available all day)
# No additional constraints needed for Natalie

# Constraints for Christine
blocked_christine = [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15]  # 9:00-11:30, 13:30-17:00
for i in time_slots:
    if i in blocked_christine:
        solver.add(christine[i] == False)

# Constraints for Vincent
blocked_vincent = [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14]  # 9:00-9:30, 10:30-12:00, 12:30-14:00, 14:30-17:00
for i in time_slots:
    if i in blocked_vincent:
        solver.add(vincent[i] == False)

# Define a variable for the start time of the meeting
meeting_start = Int('meeting_start')

# Add constraints to ensure the meeting start time is within valid range
solver.add(meeting_start >= 0)
solver.add(meeting_start <= 14)  # Last possible start is 16:00

# Ensure the selected slot is available for all participants
solver.add(gregory[meeting_start])
solver.add(natalie[meeting_start])
solver.add(christine[meeting_start])
solver.add(vincent[meeting_start])

# Ensure the next slot is also available for all participants (to cover the 30-minute duration)
solver.add(gregory[meeting_start + 1])
solver.add(natalie[meeting_start + 1])
solver.add(christine[meeting_start + 1])
solver.add(vincent[meeting_start + 1])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_start_value = model.evaluate(meeting_start).as_long()
    start_time = f"{9 + meeting_start_value // 2}:{'00' if meeting_start_value % 2 == 0 else '30'}"
    end_time = f"{9 + (meeting_start_value + 1) // 2}:{'00' if (meeting_start_value + 1) % 2 == 0 else '30'}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")