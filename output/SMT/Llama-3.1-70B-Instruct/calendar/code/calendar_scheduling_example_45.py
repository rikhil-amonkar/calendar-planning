from z3 import *

# Define the participants and their schedules
participants = ['Andrew', 'Grace', 'Samuel']
schedules = {
    'Andrew': [],
    'Grace': [],
    'Samuel': [(9*60, 10*60 + 30), (11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60, 16*60), (16*60 + 30, 17*60)],
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
    
    # Day constraint (in this case, Monday)
    day == 0,  # 0 represents Monday
    
    # Schedule constraints for each participant
    Or([And(Or([And(start_time < schedule[0], end_time <= schedule[0]),
                 And(start_time >= schedule[1], end_time > schedule[1]) 
                ])) for participant in participants for schedule in schedules[participant]]),
]

# Create a Z3 solver
solver = Solver()

# Add the constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Add a soft constraint to meet at the earliest availability
earliest_time = Int('earliest_time')
solver.add_soft(earliest_time == start_time, 100)

# Check if the solver can find a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    solution = (model[day].as_long(), model[start_time].as_long(), model[end_time].as_long())
    
    # Convert the solution to a human-readable format
    day_map = {0: 'Monday', 1: 'Tuesday', 2: 'Wednesday', 3: 'Thursday', 4: 'Friday'}
    solution_day = day_map[solution[0]]
    solution_start_time = f"{solution[1] // 60}:{solution[1] % 60:02d}"
    solution_end_time = f"{solution[2] // 60}:{solution[2] % 60:02d}"
    
    print(f"Solution: {solution_day}, {solution_start_time}, {solution_end_time}")
else:
    print("No solution found.")