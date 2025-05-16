from z3 import *

# Define the participants and their schedules
participants = ['Julie', 'Ruth']
schedules = {
    'Julie': {
        'Monday': [],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
    },
    'Ruth': {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 17*60)],
        'Thursday': [(9*60, 11*60), (11*60 + 30, 14*60 + 30), (15*60, 17*60)],
    },
}

# Define the meeting duration
meeting_duration = 30

# Define the work hours
work_hours = (9*60, 17*60)

# Create Z3 variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Create Z3 constraints
constraints = [
    # Meeting duration constraint
    end_time - start_time == meeting_duration,
    
    # Work hours constraint
    And(start_time >= work_hours[0], end_time <= work_hours[1]),
    
    # Day constraint (in this case, either Monday, Tuesday, Wednesday or Thursday)
    Or([day == i for i in range(4)]),
    
    # Schedule constraints for each participant
    Or([And(Or([And(start_time < schedule[0], end_time <= schedule[0]),
                 And(start_time >= schedule[1], end_time > schedule[1]) 
                ])) for participant in participants for day_name in schedules[participant] for schedule in schedules[participant][day_name]]),
    
    # Additional constraint for Julie
    Or([And(day!= 3, True), And(day == 3, start_time >= 11*60 + 30)]),
]

# Create a Z3 solver
solver = Solver()

# Add the constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Check if the solver can find a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    solution = (model[day].as_long(), model[start_time].as_long(), model[end_time].as_long())
    
    # Convert the solution to a human-readable format
    day_map = {0: 'Monday', 1: 'Tuesday', 2: 'Wednesday', 3: 'Thursday'}
    solution_day = day_map[solution[0]]
    solution_start_time = f"{solution[1] // 60}:{solution[1] % 60:02d}"
    solution_end_time = f"{solution[2] // 60}:{solution[2] % 60:02d}"
    
    print(f"Solution: {solution_day}, {solution_start_time}, {solution_end_time}")
else:
    print("No solution found.")