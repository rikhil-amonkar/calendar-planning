from z3 import *

# Define the days of the week as integers
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = list(range(16))  # 9:00, 9:30, ..., 16:30

# Create a Z3 solver instance
solver = Solver()

# Define variables for the day and time slot
day = Int('day')
start_time_slot = Int('start_time_slot')

# Constraints for the day
solver.add(day >= MONDAY)
solver.add(day <= WEDNESDAY)

# Constraints for the time slot
solver.add(start_time_slot >= 0)
solver.add(start_time_slot <= 14)  # Last possible start is 16:00 to accommodate 30-minute meeting

# Function to convert time slot to actual time
def time_slot_to_time(slot):
    hour = 9 + slot // 2
    minute = (slot % 2) * 30
    return f"{hour:02}:{minute:02}"

# Ronald's blocked times
ronald_blocked_times = {
    MONDAY: [2, 4, 11],  # 10:30, 12:00, 15:30
    TUESDAY: [0, 4, 11],  # 9:00, 12:00, 15:30
    WEDNESDAY: [1, 2, 5, 7, 13]  # 9:30, 11:00, 12:30, 13:30, 16:30
}

# Amber's blocked times
amber_blocked_times = {
    MONDAY: [0, 1, 3, 5, 9, 11],  # 9:00, 9:30, 11:30, 12:30, 14:30, 15:30
    TUESDAY: [0, 1, 4, 7, 13],  # 9:00, 9:30, 12:00, 13:30, 16:30
    WEDNESDAY: [0, 1, 2, 6, 10]  # 9:00, 9:30, 11:00, 15:00, 15:30
}

# Add constraints to avoid blocked times
for d in range(3):
    for t in ronald_blocked_times[d]:
        solver.add(Or(day != d, start_time_slot != t, start_time_slot != t - 1))
    for t in amber_blocked_times[d]:
        solver.add(Or(day != d, start_time_slot != t, start_time_slot != t - 1))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][model[day].as_long()]
    meeting_start_time_slot = model[start_time_slot].as_long()
    meeting_start_time = time_slot_to_time(meeting_start_time_slot)
    meeting_end_time = time_slot_to_time(meeting_start_time_slot + 1)
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")