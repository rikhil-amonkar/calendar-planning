from z3 import *

# Define the variables
day = 'Monday'
start_time = 9 * 60  # Convert 9:00 to minutes
end_time = 17 * 60   # Convert 17:00 to minutes
duration = 30        # Meeting duration in minutes
adam_schedule = [14 * 60, 15 * 60]
john_schedule = [13 * 60, 13 * 60 + 30, 14 * 60, 14 * 60 + 30, 15 * 60 + 30, 16 * 60]
stephanie_schedule = [9 * 60 + 30, 10 * 60, 10 * 60 + 30, 11 * 60, 11 * 60 + 30, 16 * 60]
anna_schedule = [9 * 60 + 30, 12 * 60, 13 * 60, 15 * 60 + 30, 16 * 60]
anna_preference = 14 * 60  # Anna would rather not meet before 14:30

# Create Z3 solver
solver = Solver()

# Define the start time variable
start = Int('start')
solver.add(start >= 9 * 60)  # Start time must be after 9:00
solver.add(start <= 16 * 60)  # Start time must be before 16:00

# Define the end time variable
end = start + duration

# Add constraints for each participant
solver.add(start + duration > adam_schedule[0])
solver.add(end <= adam_schedule[1])

solver.add(start + duration > john_schedule[0])
solver.add(start + duration <= john_schedule[1])

solver.add(start + duration > stephanie_schedule[0])
solver.add(end <= min(stephanie_schedule[1], 16 * 60))  # End time must be before 16:00

solver.add(start + duration > anna_schedule[0])
solver.add(end <= anna_schedule[1])

# Add constraint for Anna's preference
solver.add(start >= anna_preference)

# Add constraint to find a time slot that works for everyone
for hour in range(9, 17):
    time = hour * 60
    if (time + duration > adam_schedule[0] and time + duration <= adam_schedule[1] and
        time + duration > john_schedule[0] and time + duration <= min(john_schedule[1], 16 * 60) and
        time + duration > stephanie_schedule[0] and time + duration <= min(stephanie_schedule[1], 16 * 60) and
        time + duration > anna_schedule[0] and time + duration <= anna_schedule[1] and
        time >= anna_preference):
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {hour:02d}:{time % 60:02d}')
        print(f'End Time: {(hour + 1) % 24:02d}:{(time + duration) % 60:02d}')
        break
else:
    print('No solution exists.')