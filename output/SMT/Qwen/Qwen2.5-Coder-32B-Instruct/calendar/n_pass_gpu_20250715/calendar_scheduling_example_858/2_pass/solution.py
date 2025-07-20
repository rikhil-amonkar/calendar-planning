from z3 import *

# Define the days of the week as integers
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2
THURSDAY = 3

# Define the time slots in 30-minute increments from 9:00 to 17:00
TIME_SLOTS = list(range(16))  # 16 slots from 0 (9:00) to 15 (16:30)

# Create a solver instance
solver = Solver()

# Define variables for the day and time slot of the meeting
day = Int('day')
time_slot = Int('time_slot')

# Add constraints for the day
solver.add(day >= MONDAY)
solver.add(day <= THURSDAY)

# Add constraints for the time slot
solver.add(time_slot >= 0)
solver.add(time_slot <= 14)  # Ensure there is enough time for a 1-hour meeting (16 - 1 = 15, but we need to leave room for 1-hour duration)

# Convert time slot to actual time for readability
def time_slot_to_time(ts):
    return f"{9 + ts // 2}:{'00' if ts % 2 == 0 else '30'}"

# Define Carl's busy times
carl_busy_times = {
    MONDAY: [(11, 11.5)],
    TUESDAY: [(14.5, 15)],
    WEDNESDAY: [(10, 11.5), (13, 13.5)],
    THURSDAY: [(13.5, 14), (16, 16.5)]
}

# Define Margaret's busy times
margaret_busy_times = {
    MONDAY: [(9, 10.5), (11, 17)],
    TUESDAY: [(9.5, 12), (13.5, 14), (15.5, 17)],
    WEDNESDAY: [(9.5, 12), (12.5, 13), (13.5, 14.5), (15, 17)],
    THURSDAY: [(10, 12), (12.5, 14), (14.5, 17)]
}

# Add constraints for Carl's busy times
for d, busy_times in carl_busy_times.items():
    for start, end in busy_times:
        start_slot = int((start - 9) * 2)
        end_slot = int((end - 9) * 2)
        solver.add(Or(day != d, Or(time_slot < start_slot, time_slot + 2 > end_slot)))

# Add constraints for Margaret's busy times
for d, busy_times in margaret_busy_times.items():
    for start, end in busy_times:
        start_slot = int((start - 9) * 2)
        end_slot = int((end - 9) * 2)
        solver.add(Or(day != d, Or(time_slot < start_slot, time_slot + 2 > end_slot)))

# Add preference that Carl would like to avoid more meetings on Thursday
solver.add(day != THURSDAY)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_time_slot = model[time_slot].as_long()
    
    # Map the day integer to the day name
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_day_name = day_names[meeting_day]
    
    # Convert the time slot to a readable time format
    meeting_start_time = time_slot_to_time(meeting_time_slot)
    meeting_end_time = time_slot_to_time(meeting_time_slot + 2)  # Meeting duration is 1 hour
    
    print(f"SOLUTION:\nDay: {meeting_day_name}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")