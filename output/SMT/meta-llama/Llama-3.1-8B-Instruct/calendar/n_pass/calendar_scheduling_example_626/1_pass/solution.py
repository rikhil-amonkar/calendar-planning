from z3 import *

def schedule_meeting(patricia_schedule, jesse_schedule, meeting_duration):
    # Create Z3 variables for day and time
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the day variable
    day_values = [1, 2]  # 1 for Monday, 2 for Tuesday
    day_val = IntVal(day_values[0])  # Initialize with Monday
    day_eq = And(day == day_val)

    # Define the time variable
    start_time_values = [9, 10, 11, 12, 13, 14, 15, 16]
    end_time_values = [10, 11, 12, 13, 14, 15, 16, 17]
    start_time_val = IntVal(start_time_values[0])
    end_time_val = IntVal(end_time_values[0])
    time_eq = And(start_time == start_time_val, end_time == end_time_val)

    # Define the constraints for Patricia's schedule
    patricia_constraints = []
    for patricia_start, patricia_end in patricia_schedule:
        patricia_constraint = Or(
            And(start_time < patricia_start, end_time < patricia_start),
            And(start_time > patricia_end, end_time > patricia_end),
            And(start_time >= patricia_start, start_time < patricia_end),
            And(end_time > patricia_start, end_time <= patricia_end)
        )
        patricia_constraints.append(patricia_constraint)

    # Define the constraints for Jesse's schedule
    jesse_constraints = []
    for jesse_start, jesse_end in jesse_schedule:
        jesse_constraint = Or(
            And(start_time < jesse_start, end_time < jesse_start),
            And(start_time > jesse_end, end_time > jesse_end),
            And(start_time >= jesse_start, start_time < jesse_end),
            And(end_time > jesse_start, end_time <= jesse_end)
        )
        jesse_constraints.append(jesse_constraint)

    # Define the constraint for the meeting duration
    meeting_duration_constraint = And(end_time - start_time == meeting_duration)

    # Define the solver and add constraints
    solver = Solver()
    solver.add(day_eq)
    solver.add(time_eq)
    solver.add(And(patricia_constraints))
    solver.add(And(jesse_constraints))
    solver.add(meeting_duration_constraint)

    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        day = model[day].as_long()
        start_time = model[start_time].as_long()
        end_time = model[end_time].as_long()
        return f"SOLUTION:\nDay: {['Monday', 'Tuesday'][day - 1]}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00"
    else:
        return "No solution found"

# Example usage
patricia_schedule = [(10, 10.5), (11.5, 12), (13, 13.5), (14.5, 15.5), (16, 16.5)]
jesse_schedule = [(9, 17), (11, 11.5), (12, 12.5), (13, 14), (14.5, 15), (15.5, 17)]
meeting_duration = 1
print(schedule_meeting(patricia_schedule, jesse_schedule, meeting_duration))