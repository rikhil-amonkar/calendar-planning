from z3 import *

def schedule_meeting(evelyn_availability, randy_availability, meeting_duration, evelyn_preferences):
    # Create a Z3 solver
    solver = Solver()

    # Define the day, start time, and end time variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the day of the week (0 = Monday, 1 = Tuesday,..., 6 = Sunday)
    days_of_week = [day == 0]  # We are only scheduling for Monday

    # Define the start and end times for each day (in 30-minute increments)
    times_of_day = [start_time >= 180, start_time < 24*60, end_time >= 180, end_time < 24*60]

    # Add constraints for Evelyn's availability
    evelyn_constraints = []
    for time in evelyn_availability:
        evelyn_constraints.append(Or(start_time < time[0], start_time >= time[1]))
    for time in evelyn_preferences:
        evelyn_constraints.append(Or(start_time < time[0], start_time >= time[1]))

    # Add constraints for Randy's availability
    randy_constraints = []
    for time in randy_availability:
        randy_constraints.append(Or(start_time < time[0], start_time >= time[1]))

    # Add constraints for the meeting duration
    meeting_constraints = [end_time == start_time + meeting_duration]

    # Add all constraints to the solver
    solver.add(days_of_week)
    solver.add(times_of_day)
    solver.add(evelyn_constraints)
    solver.add(randy_constraints)
    solver.add(meeting_constraints)

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()

        # Convert the start and end times to 24-hour format
        hours = start_time_value // 60
        minutes = start_time_value % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        hours = end_time_value // 60
        minutes = end_time_value % 60
        end_time_str = f"{hours:02d}:{minutes:02d}"

        # Print the solution
        print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
    else:
        print("No solution exists.")

# Example usage:
evelyn_availability = [(180, 240)]  # 9:00-17:00
randy_availability = [(180, 210), (240, 300)]  # 9:00-10:30, 16:00-17:00
meeting_duration = 30  # 30 minutes
evelyn_preferences = [(120, 210)]  # 13:00-14:30

schedule_meeting(evelyn_availability, randy_availability, meeting_duration, evelyn_preferences)