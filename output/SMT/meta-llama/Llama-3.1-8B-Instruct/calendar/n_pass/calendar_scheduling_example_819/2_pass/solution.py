from z3 import *

def schedule_meeting():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Define the start and end times
    start_times = [9, 10, 11, 11.5, 12, 13, 14, 14.5, 15, 15.5, 16, 16.5, 17]
    end_times = [9.5, 10.5, 11.5, 12, 12.5, 13.5, 14.5, 15, 15.5, 16, 16.5, 17, 17.5]

    # Create Z3 variables for the meeting day, start time, and end time
    day = Int('day')
    start_time = Real('start_time')
    end_time = Real('end_time')

    # Create Z3 constraints for the meeting day
    day_domain = [day!= 1, day!= 2, day!= 3]  # Julie has no meetings the whole week
    day_domain = [Or([day == i for i in range(4)])]  # Ruth is busy on Monday, Tuesday, Wednesday
    day_domain = [day!= 0 or (start_time >= 11.5 and end_time <= 17)]  # Julie would like to avoid more meetings on Thursday before 11:30

    # Create Z3 constraints for the start and end times
    start_time_domain = [start_time >= 9, start_time <= 17]
    end_time_domain = [end_time >= start_time, end_time <= 17.5]

    # Create Z3 constraints for the meeting duration
    duration = [end_time - start_time == 0.5]

    # Create Z3 constraints for Ruth's schedule
    ruth_schedule = [start_time >= 9, start_time <= 17,  # Monday
                     start_time >= 9, start_time <= 17,  # Tuesday
                     start_time >= 9, start_time <= 17,  # Wednesday
                     start_time >= 11, start_time <= 11.5, start_time >= 14.5, start_time <= 17]  # Thursday

    # Create Z3 constraints for Julie's preference
    julie_preference = [start_time >= 11.5]

    # Create the Z3 solver and add the constraints
    solver = Solver()
    solver.add(And(day_domain, start_time_domain, end_time_domain, duration, ruth_schedule, julie_preference))

    # Solve the Z3 constraints
    if solver.check() == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_time_value = model[start_time].numeral().as_real()
        end_time_value = model[end_time].numeral().as_real()
        day_name = days[day_value]
        start_time = str(int(start_time_value * 2)) + ':00'
        end_time = str(int(end_time_value * 2)) + ':00'
        return f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time}\nEnd Time: {end_time}"
    else:
        return "No solution found"

print(schedule_meeting())