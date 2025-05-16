from z3 import *

# Define the participants and their schedules
participants = ['Russell', 'Alexander']
schedules = {
    'Russell': {
        'Monday': [(10*60 + 30, 11*60)],
        'Tuesday': [(13*60, 13*60 + 30)],
    },
    'Alexander': {
        'Monday': [(9*60, 11*60 + 30), (12*60, 14*60 + 30), (15*60, 17*60)],
        'Tuesday': [(9*60, 10*60), (13*60, 14*60), (15*60, 15*60 + 30), (16*60, 16*60 + 30)],
    },
}

# Define the meeting duration
meeting_duration = 60

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
    
    # Day constraint (in this case, either Monday or Tuesday)
    Or([day == i for i in range(2)]),
    
    # Schedule constraints for each participant
    Or([And(Or([And(start_time < schedule[0], end_time <= schedule[0]),
                 And(start_time >= schedule[1], end_time > schedule[1]) 
                ])) for participant in participants for day_name in schedules[participant] for schedule in schedules[participant][day_name]]),
    
    # Additional constraint for Russell
    Or([And(day!= 1, True), And(day == 1, start_time >= 13*60 + 30)]),
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
    day_map = {0: 'Monday', 1: 'Tuesday'}
    solution_day = day_map[solution[0]]
    solution_start_time = f"{solution[1] // 60}:{solution[1] % 60:02d}"
    solution_end_time = f"{solution[2] // 60}:{solution[2] % 60:02d}"
    
    print(f"Solution: {solution_day}, {solution_start_time}, {solution_end_time}")
else:
    print("No solution found.")