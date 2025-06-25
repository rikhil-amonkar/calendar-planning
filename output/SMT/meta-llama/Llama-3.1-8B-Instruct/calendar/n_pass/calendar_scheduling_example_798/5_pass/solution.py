from z3 import *

def schedule_meeting(nancy_schedule, jose_schedule, meeting_duration):
    # Create Z3 variables for days and times
    days = [Int("day") for _ in range(3)]
    for i, day in enumerate(days):
        day.range = (i, i)
        day.sort = IntSort()

    times = [Int("time") for _ in range(48)]
    for i, time in enumerate(times):
        time.range = (i, i)
        time.sort = IntSort()

    # Create Z3 variables for meeting start and end times
    start_time = Int("start_time")
    end_time = Int("end_time")

    # Define the constraints for the meeting duration
    duration_constraint = Implies(start_time < end_time, end_time - start_time == meeting_duration)

    # Define the constraints for Nancy's schedule
    nancy_constraints = []
    for nancy_time in nancy_schedule:
        start, end = nancy_time
        start_hour = start // 60
        end_hour = end // 60
        start_minute = start % 60
        end_minute = end % 60
        nancy_constraints.append(Or(start_time < start_hour*60 + start_minute, end_hour*60 + end_minute < start_time))
        nancy_constraints.append(Or(start_time < end_hour*60 + end_minute, end_time < end_hour*60 + end_minute))

    # Define the constraints for Jose's schedule
    jose_constraints = []
    for jose_time in jose_schedule:
        start, end = jose_time
        start_hour = start // 60
        end_hour = end // 60
        start_minute = start % 60
        end_minute = end % 60
        jose_constraints.append(Or(start_time < start_hour*60 + start_minute, end_hour*60 + end_minute < start_time))
        jose_constraints.append(Or(start_time < end_hour*60 + end_minute, end_time < end_hour*60 + end_minute))

    # Define the constraints for the day
    day_constraints = []
    for day in days:
        day_constraints.append(And(start_time >= 9*60, start_time < 17*60))
        day_constraints.append(And(end_time > start_time, end_time <= 17*60))

    # Define the constraints for the meeting time
    for day in days:
        solver = Solver()
        solver.add(day == 0) # Choose Monday as the default day
        for i in range(48):
            time_constraints = []
            time_constraints.append(And(start_time >= i, start_time < i + 30))
            time_constraints.append(And(end_time > i, end_time <= i + 30))
            solver.add(And(duration_constraint, *nancy_constraints, *jose_constraints, *day_constraints, *time_constraints))
            if solver.check() == sat:
                model = solver.model()
                start_time_value = model[start_time].as_long()
                end_time_value = model[end_time].as_long()
                return f"SOLUTION:\nDay: Monday\nStart Time: {start_time_value//60:02d}:{start_time_value%60:02d}\nEnd Time: {end_time_value//60:02d}:{end_time_value%60:02d}"
    return "No solution found"

# Example usage
nancy_schedule = [(10, 10.5), (11.5, 12.5), (13.5, 14), (14.5, 15.5), (16, 17), 
                  (9.5, 10.5), (11, 11.5), (12, 12.5), (13, 13.5), (15.5, 16),
                  (10, 11.5), (13.5, 16)]
jose_schedule = [(9, 17), (9, 17), (9, 9.5), (10, 12.5), (13.5, 14.5), (15, 17)]
meeting_duration = 30

print(schedule_meeting(nancy_schedule, jose_schedule, meeting_duration))