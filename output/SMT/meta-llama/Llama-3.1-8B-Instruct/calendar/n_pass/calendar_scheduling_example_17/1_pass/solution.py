from z3 import *

def schedule_meeting(margaret_schedule, donna_schedule, helen_schedule, max_duration=30, day='Monday'):
    # Create Z3 variables
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define constraints
    constraints = [
        And(start_time >= 9 * 60, start_time <= 17 * 60),  # Start time within work hours
        And(end_time >= start_time + max_duration, end_time <= 17 * 60),  # End time within work hours and at least max_duration minutes after start time
        Not(Or(And(start_time >= 9 * 60, start_time < 10 * 60, end_time > 10 * 60),  # Margaret's first block
               And(start_time >= 10 * 60, start_time < 10 * 30 + max_duration, end_time > 11 * 60),  # Margaret's second block
               And(start_time >= 11 * 60, start_time < 12 * 60, end_time > 12 * 60),  # Margaret's third block
               And(start_time >= 13 * 60, start_time < 13 * 30 + max_duration, end_time > 13 * 60),  # Margaret's fourth block
               And(start_time >= 15 * 60, start_time < 15 * 30 + max_duration, end_time > 15 * 60),  # Margaret's fifth block
               And(start_time >= 14 * 60, start_time < 15 * 60, end_time > 15 * 60),  # Donna's first block
               And(start_time >= 16 * 60, start_time < 16 * 30 + max_duration, end_time > 16 * 60),  # Donna's second block
               And(start_time >= 9 * 60, start_time < 9 * 30 + max_duration, end_time > 9 * 60),  # Helen's first block
               And(start_time >= 10 * 60, start_time < 11 * 30 + max_duration, end_time > 11 * 60),  # Helen's second block
               And(start_time >= 13 * 60, start_time < 14 * 60, end_time > 14 * 60),  # Helen's third block
               And(start_time >= 14 * 60, start_time < 15 * 60, end_time > 15 * 60),  # Helen's fourth block
               And(start_time >= 15 * 60, start_time < 17 * 60, end_time > 17 * 60),  # Helen's fifth block
               And(start_time >= 13 * 30 + max_duration, end_time < 14 * 60),  # Helen does not want to meet after 13:30
               )
    ]

    # Add Z3 solver
    s = Solver()

    # Add constraints to solver
    for constraint in constraints:
        s.add(constraint)

    # Solve
    if s.check() == sat:
        model = s.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}"
    else:
        return "No solution found"

# Example usage
margaret_schedule = [9 * 60, 10 * 60, 10 * 30, 11 * 60, 11 * 30, 13 * 60, 13 * 30, 15 * 60, 15 * 30]
donna_schedule = [14 * 60, 14 * 30, 16 * 60, 16 * 30]
helen_schedule = [9 * 60, 9 * 30, 10 * 60, 11 * 30, 13 * 60, 14 * 60, 14 * 30, 15 * 60, 15 * 30, 17 * 60]

print(schedule_meeting(margaret_schedule, donna_schedule, helen_schedule))