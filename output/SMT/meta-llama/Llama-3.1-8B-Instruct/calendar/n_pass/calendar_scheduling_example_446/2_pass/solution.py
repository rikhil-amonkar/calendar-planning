from z3 import *

# Define the variables
day = 'Monday'
meeting_duration = 30  # in minutes

# Define the existing schedules
schedules = {
    'Megan': [(9, 30), (10, 60), (12, 30)],
    'Christine': [(9, 30), (11*60, 12*60), (13*60, 14*60), (15*30, 16*30)],
    'Gabriel': [],
    'Sara': [(11*60, 12*60), (14*30, 15*30)],
    'Bruce': [(9*30, 10*30), (10*30, 12*60), (12*30, 14*60), (14*30, 15*30), (15*30, 16*30)],
    'Kathryn': [(10, 15*30), (16, 16*30)],
    'Billy': [(9, 30), (11, 11*30), (12, 14*60), (14*30, 15*30)]
}

# Define the solver
solver = Solver()

# Define the start time variable
start_time = Int('start_time')

# Add constraints for the work hours
solver.add(9 * 60 <= start_time)
solver.add(start_time + meeting_duration <= 17 * 60)

# Define the end time variable
end_time = start_time + meeting_duration

# Add constraints for each participant
for participant, schedule in schedules.items():
    for start, end in schedule:
        solver.add(start * 60 <= start_time)
        solver.add(end_time <= end * 60)

# Check the solution
if solver.check() == sat:
    model = solver.model()
    print(f'SOLUTION:')
    print(f'Day: {day}')
    print(f'Start Time: {model[start_time].as_string().split(":")[0]}:{model[start_time].as_string().split(":")[1]}')
    print(f'End Time: {model[end_time].as_string().split(":")[0]}:{model[end_time].as_string().split(":")[1]}')
else:
    print('No solution found')

    # Try all possible time slots
    for start in range(9 * 60, 17 * 60 - meeting_duration):
        end = start + meeting_duration
        conflict = False
        for participant, schedule in schedules.items():
            for s, e in schedule:
                if start < s * 60 and end > s * 60:
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            print(f'SOLUTION:')
            print(f'Day: {day}')
            print(f'Start Time: {start // 60}:{start % 60}')
            print(f'End Time: {(end // 60):02d}:{(end % 60):02d}')
            break