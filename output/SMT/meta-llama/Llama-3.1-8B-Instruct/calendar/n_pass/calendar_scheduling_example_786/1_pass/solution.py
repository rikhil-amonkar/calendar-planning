from z3 import *

# Define the variables
days = ['Monday', 'Tuesday', 'Wednesday']
start_times = [9*60 + i for i in range(30, 17*60, 30)]
end_times = [(st + 30) for st in start_times]

# Define the constraints for each person
amy_busy = [
    (And(10*60 <= st, st <= 11*60), 11*60 <= et <= 11*30),  # Wednesday 11:00-11:30
    (And(13*60 <= st, st <= 14*60), 13*60 <= et <= 14*00)  # Wednesday 13:30-14:00
]

pamela_busy = [
    (And(9*60 <= st, st <= 10*60), 9*60 <= et <= 10*30),  # Monday 9:00-10:30
    (And(11*60 <= st, st <= 16*60), 11*60 <= et <= 16*30),  # Monday 11:00-16:30
    (And(9*60 <= st, st <= 9*60 + 30), 9*60 <= et <= 9*30),  # Tuesday 9:00-9:30
    (And(10*60 <= st, st <= 17*60), 10*60 <= et <= 17*00),  # Tuesday 10:00-17:00
    (And(9*60 <= st, st <= 10*60), 9*60 <= et <= 10*00),  # Wednesday 9:00-10:00
    (And(11*60 <= st, st <= 11*60 + 30), 11*60 <= et <= 11*30),  # Wednesday 11:30-12:00
    (And(13*60 <= st, st <= 14*60), 13*60 <= et <= 13*30),  # Wednesday 13:30-14:00
    (And(14*60 <= st, st <= 15*60), 14*60 <= et <= 15*00),  # Wednesday 14:30-15:00
    (And(16*60 <= st, st <= 16*60 + 30), 16*60 <= et <= 16*30)  # Wednesday 16:00-16:30
]

pamela_preferred = [
    (And(And(day!= 'Monday', day!= 'Tuesday'), st >= 16*60), False)  # Avoid meetings on Monday, Tuesday before 16:00
]

# Define the solver
s = Solver()

# Define the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Add the constraints
for d, st, et in zip(days, start_times, end_times):
    s.add(And(0 <= day < 3, 0 <= start_time < 24*60, 0 <= end_time < 24*60, 
              Or(day == 0, Or(day == 1, day == 2)),
              Or(start_time == st, start_time == et),
              Or(end_time == st + 30, end_time == et),
              (day, start_time, end_time) not in amy_busy,
              (day, start_time, end_time) not in pamela_busy,
              (day, start_time, end_time) not in pamela_preferred))

# Check for a solution
s.check()

# Get the solution
model = s.model()

# Print the solution
print('SOLUTION:')
print(f'Day: {days[model[day].as_long()]}')
print(f'Start Time: {model[start_time].as_long() // 60:02d}:{model[start_time].as_long() % 60:02d}')
print(f'End Time: {model[end_time].as_long() // 60:02d}:{model[end_time].as_long() % 60:02d}')