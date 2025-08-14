from z3 import *

# Define the time slots as integers from 0 to 16 (representing 9:00 to 17:00 in 30-minute increments)
time_slots = range(16)

# Create a solver instance
solver = Solver()

# Define the meeting start time as an integer variable
meeting_start_time = Int('meeting_start_time')

# Define the constraints for each participant
cynthia_busy_slots = {3, 4, 6, 10, 11}  # 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00
lauren_busy_slots = {0, 2, 3, 4, 6, 8, 9, 10, 12, 13, 16}  # 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
robert_busy_slots = {2, 3, 4, 8, 9, 10, 11, 12, 13, 14}  # 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00

# Add constraints to ensure the meeting time is within the working hours and not during busy times
solver.add(meeting_start_time >= 0)
solver.add(meeting_start_time <= 13)  # 13 represents 12:00, so the latest start time is 12:00 to 12:30

# Ensure the meeting does not overlap with busy slots
for slot in cynthia_busy_slots:
    solver.add(And(meeting_start_time != slot, meeting_start_time + 1 != slot))
for slot in lauren_busy_slots:
    solver.add(And(meeting_start_time != slot, meeting_start_time + 1 != slot))
for slot in robert_busy_slots:
    solver.add(And(meeting_start_time != slot, meeting_start_time + 1 != slot))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_time_slot = model[meeting_start_time].as_long()
    meeting_start_time = 9 + meeting_start_time_slot // 2
    meeting_end_time = meeting_start_time + 0.5

    # Convert times to HH:MM format
    start_time_str = f"{int(meeting_start_time):02}:{int((meeting_start_time % 1) * 60):02}"
    end_time_str = f"{int(meeting_end_time):02}:{int((meeting_end_time % 1) * 60):02}"

    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")