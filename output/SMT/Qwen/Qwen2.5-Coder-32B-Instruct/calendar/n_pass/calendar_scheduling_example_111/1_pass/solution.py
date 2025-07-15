from z3 import *

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [900 + i * 30 for i in range(16)]  # This gives us times from 9:00 to 16:30

# Create a Z3 solver instance
solver = Solver()

# Define boolean variables for each person for each time slot
gregory_vars = [Bool(f'gregory_{t}') for t in time_slots]
natalie_vars = [Bool(f'natalie_{t}') for t in time_slots]
christine_vars = [Bool(f'christine_{t}') for t in time_slots]
vincent_vars = [Bool(f'vincent_{t}') for t in time_slots]

# Add constraints for each person based on their schedule
# Gregory is busy during 9:00-10:00, 10:30-11:30, 12:30-13:00, 13:30-14:00
for t in time_slots:
    if 900 <= t < 1000 or 1030 <= t < 1130 or 1230 <= t < 1300 or 1330 <= t < 1400:
        solver.add(Not(gregory_vars[time_slots.index(t)]))

# Natalie is free all day
for t in time_slots:
    solver.add(natalie_vars[time_slots.index(t)])

# Christine is busy during 9:00-11:30, 13:30-17:00
for t in time_slots:
    if 900 <= t < 1130 or 1330 <= t < 1700:
        solver.add(Not(christine_vars[time_slots.index(t)]))

# Vincent is busy during 9:00-9:30, 10:30-12:00, 12:30-14:00, 14:30-17:00
for t in time_slots:
    if 900 <= t < 930 or 1030 <= t < 1200 or 1230 <= t < 1400 or 1430 <= t < 1700:
        solver.add(Not(vincent_vars[time_slots.index(t)]))

# Add constraints to ensure that the meeting time is available for all participants
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# The meeting duration is 30 minutes
solver.add(meeting_end == meeting_start + 30)

# The meeting must start and end within the working hours (9:00 to 17:00)
solver.add(meeting_start >= 900)
solver.add(meeting_end <= 1700)

# The meeting must be available for all participants
for t in time_slots:
    solver.add(Implies(meeting_start == t, And(gregory_vars[time_slots.index(t)], natalie_vars[time_slots.index(t)], christine_vars[time_slots.index(t)], vincent_vars[time_slots.index(t)])))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = model[meeting_end].as_long()
    
    # Convert the time back to HH:MM format
    start_hour = meeting_start_time // 100
    start_minute = meeting_start_time % 100
    end_hour = meeting_end_time // 100
    end_minute = meeting_end_time % 100
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")