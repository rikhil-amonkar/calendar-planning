from z3 import *

def schedule_meeting(jeffrey_schedule, virginia_schedule, melissa_schedule, meeting_duration, melissa_preference):
    # Create a new solver
    s = Solver()

    # Define the day to meet
    day = 'Monday'

    # Define the start and end time variables
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for the day to meet
    s.add(And(start_time >= 9*60, start_time <= 17*60))
    s.add(end_time >= 9*60, end_time <= 17*60)

    # Add constraints for the meeting duration
    s.add(And(end_time - start_time == meeting_duration * 60))

    # Add constraints for the existing schedules
    for time in [9*60 + 30, 10*60]:
        s.add(Or(start_time > time, end_time < time))
    for time in [9*60, 10*60, 14*60 + 30, 16*60]:
        s.add(Or(start_time > time, end_time < time))
    for time in [9*60, 11*60, 12*60, 13*60, 16*60]:
        s.add(Or(start_time > time, end_time < time))

    # Add constraints for the conflict on Monday from 9 to 11.5
    s.add(And(start_time >= 11.5*60, end_time <= 11.5*60))

    # Add constraints for Melissa's preference
    if melissa_preference:
        s.add(start_time <= 14*60)

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        model = s.model()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()

        # Return the solution in the required format
        return f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}\nEnd Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}"
    else:
        return "No solution exists"

# Example usage
jeffrey_schedule = [9*60 + 30, 10*60]
virginia_schedule = [9*60, 10*60, 14*60 + 30, 16*60]
melissa_schedule = [9*60, 11*60, 12*60, 13*60, 16*60]
meeting_duration = 0.5
melissa_preference = True

print(schedule_meeting(jeffrey_schedule, virginia_schedule, melissa_schedule, meeting_duration, melissa_preference))