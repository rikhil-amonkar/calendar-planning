from z3 import *

def schedule_meeting():
    # Define the days and hours
    days = ['Monday', 'Tuesday', 'Wednesday']
    hours = [9] + [i for i in range(10, 18)]  # 9:00 to 17:00

    # Define the existing schedules for Robert and Ralph
    robert_schedules = {
        'Monday': [(11, 30), (14, 30), (15, 30)],
        'Tuesday': [(10, 30), (15, 30)],
        'Wednesday': [(10, 0), (11, 30), (12, 30), (13, 30), (15, 30), (16, 0)]
    }

    ralph_schedules = {
        'Monday': [(10, 0), (14, 30), (15, 0)],
        'Tuesday': [(9, 0), (10, 0), (11, 0), (12, 0), (14, 0), (16, 0)],
        'Wednesday': [(10, 30), (11, 30), (13, 0), (16, 30)]
    }

    # Define the preferences
    robert_preferences = ['Monday', 'Tuesday', 'Wednesday']

    # Create Z3 variables
    day = Int('day')
    start_hour = Int('start_hour')
    start_minute = Int('start_minute')
    end_hour = Int('end_hour')
    end_minute = Int('end_minute')

    # Create Z3 constraints
    day_val = [day == i for i in range(len(days))]
    start_hour_val = [start_hour == i for i in hours]
    start_minute_val = [start_minute == 0]
    end_hour_val = [end_hour == start_hour + 0.5]
    end_minute_val = [end_minute == 30]

    # Constraints for Robert's schedule
    robert_constraints = []
    for d, s in robert_schedules.items():
        for st, et in s:
            robert_constraints.append(If(day_val[days.index(d)], And(start_hour_val[hours.index(st)], start_minute_val, end_hour_val[hours.index(et)], end_minute_val), True))

    # Constraints for Ralph's schedule
    ralph_constraints = []
    for d, s in ralph_schedules.items():
        for st, et in s:
            ralph_constraints.append(If(day_val[days.index(d)], And(start_hour_val[hours.index(st)], start_minute_val, end_hour_val[hours.index(et)], end_minute_val), True))

    # Constraint to avoid more meetings on Monday
    mon_day = day_val[0]
    mon_start_hour = start_hour_val[hours.index(9)]
    mon_start_minute = start_minute_val
    mon_end_hour = end_hour_val[hours.index(17)]
    mon_end_minute = end_minute_val
    mon_constraints = [mon_day, mon_start_hour, mon_start_minute, mon_end_hour, mon_end_minute]
    for st, et in robert_schedules['Monday']:
        mon_constraints.append(Not(And(mon_day, And(start_hour_val[hours.index(st)], start_minute_val, end_hour_val[hours.index(et)], end_minute_val))))

    # Constraint to choose the earliest available time
    earliest_start_hour = If(day == 0, start_hour == 9, If(day == 1, start_hour == 9, start_hour == 9))
    earliest_start_minute = start_minute_val
    earliest_end_hour = If(day == 0, end_hour == 9.5, If(day == 1, end_hour == 9.5, end_hour == 9.5))
    earliest_end_minute = end_minute_val
    earliest_constraints = [earliest_start_hour, earliest_start_minute, earliest_end_hour, earliest_end_minute]

    # Create the Z3 solver
    s = Solver()

    # Add the constraints to the solver
    s.add(robert_constraints)
    s.add(ralph_constraints)
    s.add(mon_constraints)
    s.add(earliest_constraints)

    # Solve the constraints
    if s.check() == sat:
        # Get the model
        m = s.model()

        # Extract the values from the model
        day_val = m[day].as_long()
        start_hour_val = m[start_hour].as_long()
        start_minute_val = m[start_minute].as_long()
        end_hour_val = m[end_hour].as_long()
        end_minute_val = m[end_minute].as_long()

        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {days[day_val]}")
        print(f"Start Time: {hours[start_hour_val]}:{start_minute_val:02d}")
        print(f"End Time: {hours[end_hour_val]}:{end_minute_val:02d}")
    else:
        print("No solution found.")

schedule_meeting()