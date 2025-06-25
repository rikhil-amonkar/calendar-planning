from z3 import *

# Define the variables
day = 'Monday'
start_time = 9
end_time = 17
meeting_duration = 1

# Define the time slots for each participant
danielle_slots = [(9, 10), (10.5, 11), (14.5, 15), (15.5, 16), (16.5, 17)]
bruce_slots = [(11, 11.5), (12.5, 13), (14, 14.5), (15.5, 16)]
eric_slots = [(9, 9.5), (10, 11), (11.5, 13), (14.5, 15.5)]

# Create Z3 solver
solver = Solver()

# Define the variables for the meeting time
t = Int('t')

# Define the variables for the meeting end time
t_end = Int('t_end')

# Define the constraints
for start, end in danielle_slots:
    solver.add(Or(t < start, t + meeting_duration > end))
for start, end in bruce_slots:
    solver.add(Or(t < start, t + meeting_duration > end))
for start, end in eric_slots:
    solver.add(Or(t < start, t + meeting_duration > end))

# Add constraints for the meeting duration
solver.add(t + meeting_duration <= end_time)

# Find the earliest possible start time for the meeting
earliest_start = 9
while earliest_start < end_time - meeting_duration:
    solver.push()
    solver.add(t == earliest_start)
    if solver.check() == sat:
        print(f'SOLUTION:\nDay: {day}\nStart Time: {earliest_start:02d}:00\nEnd Time: {(earliest_start + meeting_duration):02d}:00')
        solver.pop()
        break
    solver.pop()
    earliest_start += 1
else:
    print('No solution found.')