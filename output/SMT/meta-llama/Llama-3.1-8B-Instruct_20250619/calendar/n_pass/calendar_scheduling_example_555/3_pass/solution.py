from z3 import *

def schedule_meeting(evelyn_schedule, randy_schedule, meeting_duration, day, evelyn_preferences):
    # Create Z3 solver
    solver = Solver()

    # Define variables for the start time of the meeting
    start_time = Int('start_time')
    end_time = start_time + meeting_duration

    # Add constraints for the day
    solver.add(And(start_time >= 9 * 60, start_time < 17 * 60))
    solver.add(end_time <= 17 * 60)

    # Add constraints for Evelyn's schedule
    for time in evelyn_schedule:
        solver.add(And(start_time >= time[0] * 60, start_time < time[1] * 60))

    # Add constraints for Randy's schedule
    for time in randy_schedule:
        solver.add(And(start_time >= time[0] * 60, start_time < time[1] * 60))

    # Add constraints for Evelyn's preferences
    for time in evelyn_preferences:
        if time[0] <= 13:
            solver.add(And(start_time >= time[1] * 60, start_time < 13 * 60))
        else:
            solver.add(And(start_time >= 13 * 60, start_time < 17 * 60))

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        start_time_value = model[start_time].as_long() // 60
        end_time_value = (model[start_time].as_long() // 60) + meeting_duration

        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time_value:02d}:00")
        print(f"End Time: {end_time_value:02d}:00")
    else:
        print("No solution exists.")

# Example usage
evelyn_schedule = []
randy_schedule = [(9, 10.5), (11, 15.5), (16, 17)]
meeting_duration = 0.5
day = "Monday"
evelyn_preferences = [(9, 13)]

schedule_meeting(evelyn_schedule, randy_schedule, meeting_duration, day, evelyn_preferences)