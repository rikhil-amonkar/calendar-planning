from z3 import *

def schedule_meeting(schedules, meeting_duration):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    days = [Int('day')]
    start_times = [Int('start_time')]
    end_times = [Int('end_time')]

    # Add constraints for the day
    solver.add(days[0] == 0)  # Only Monday for now

    # Add constraints for the start time
    solver.add(And(9 <= start_times[0], start_times[0] + meeting_duration <= 17))

    # Add constraints for the end time
    solver.add(end_times[0] == start_times[0] + meeting_duration)

    # Add constraints for the schedules
    for i, schedule in enumerate(schedules):
        solver.add(Or(
            start_times[0] + meeting_duration > schedule[1] + 1,  # End time is after the schedule
            start_times[0] < schedule[0],  # Start time is before the schedule
            end_times[0] < schedule[0],  # End time is before the schedule
            end_times[0] > schedule[1] + 1  # Start time is after the schedule
        ))

    # Check if there is a solution
    if solver.check() == sat:
        model = solver.model()
        day_value = "Monday"
        start_time_value = str(model[start_times[0]].as_long()) + ":00"
        end_time_value = str(model[end_times[0]].as_long()) + ":00"
        return f"SOLUTION:\nDay: {day_value}\nStart Time: {start_time_value}\nEnd Time: {end_time_value}"
    else:
        return "No solution found"

# Example usage
schedules = [[11*60, 12*60], [9*60, 11*60], [11*60, 12*60], [12*30*60, 13*30*60], [14*30*60, 16*30*60]]
meeting_duration = 60
print(schedule_meeting(schedules, meeting_duration))