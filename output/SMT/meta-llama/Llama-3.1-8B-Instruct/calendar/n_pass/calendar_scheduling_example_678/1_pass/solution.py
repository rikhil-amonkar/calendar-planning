from z3 import *

def schedule_meeting():
    # Define the days of the week
    monday = 1
    tuesday = 2

    # Define the start and end times of the workday
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the meeting duration
    meeting_duration = 60

    # Define the variables
    day = Int('day')
    start_hour = Int('start_hour')
    end_hour = Int('end_hour')

    # Define the constraints for Russell's schedule
    russell_monday = And(day == monday, Or(start_hour > 11, start_hour < 10))
    russell_tuesday = And(day == tuesday, Or(start_hour > 13, start_hour < 13))
    russell_constraints = Or(russell_monday, russell_tuesday)

    # Define the constraints for Alexander's schedule
    alexander_monday = And(day == monday, 
                            Or(start_hour > 11, start_hour < 9) 
                            Or(start_hour > 14, start_hour < 12) 
                            Or(start_hour > 17, start_hour < 15))
    alexander_tuesday = And(day == tuesday, 
                            Or(start_hour > 10, start_hour < 9) 
                            Or(start_hour > 14, start_hour < 13) 
                            Or(start_hour > 16, start_hour < 15) 
                            Or(start_hour > 16, start_hour < 13))
    alexander_constraints = Or(alexander_monday, alexander_tuesday)

    # Define the constraints for the meeting duration
    meeting_constraints = And(start_hour >= start_time, 
                              start_hour + meeting_duration <= end_time, 
                              end_hour >= start_hour + meeting_duration)

    # Define the constraints for Russell's preference
    russell_preference = Or(day == tuesday, start_hour >= 13)

    # Define the solver and the constraints
    solver = Solver()
    solver.add(And(russell_constraints, alexander_constraints, meeting_constraints, russell_preference))

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        day_value = model[day].as_long()
        start_hour_value = model[start_hour].as_long()
        end_hour_value = model[end_hour].as_long()

        # Convert the hour values to 24-hour format
        start_time_value = f"{start_hour_value // 60:02d}:{start_hour_value % 60:02d}"
        end_time_value = f"{end_hour_value // 60:02d}:{end_hour_value % 60:02d}"

        # Print the solution
        print(f"SOLUTION:\nDay: {['Monday', 'Tuesday'][day_value - 1]}\nStart Time: {start_time_value}\nEnd Time: {end_time_value}")
    else:
        print("No solution found.")

schedule_meeting()