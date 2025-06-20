from z3 import *

def schedule_meeting(michael_schedule, eric_schedule, arthur_schedule, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define the day of the meeting
    day = Int('day')
    s.add(day == 1)  # Meeting is on Monday

    # Define the start and end time of the meeting
    start_hour = Int('start_hour')
    s.add(And(9 <= start_hour, start_hour <= 16))  # Start time is between 9:00 and 16:00
    end_hour = Int('end_hour')
    s.add(And(start_hour + meeting_duration[0] <= end_hour, end_hour <= 17))  # End time is between start time + meeting duration and 17:00

    # Add constraints for each participant
    s.add(Or(start_hour + meeting_duration[0] > michael_schedule[(9, 30)][0],
             start_hour + meeting_duration[0] > michael_schedule[(15, 0)][0],
             start_hour + meeting_duration[0] > michael_schedule[(16, 0)][0],
             end_hour < michael_schedule[(9, 30)][1],
             end_hour < michael_schedule[(15, 0)][1],
             end_hour < michael_schedule[(16, 0)][1]))
    s.add(Or(start_hour + meeting_duration[0] > arthur_schedule[(9, 0)][0],
             end_hour < arthur_schedule[(9, 0)][1]))
    s.add(Or(start_hour + meeting_duration[0] > arthur_schedule[(13, 0)][0],
             end_hour < arthur_schedule[(13, 0)][1]))
    s.add(Or(start_hour + meeting_duration[0] > arthur_schedule[(15, 30)][0],
             end_hour < arthur_schedule[(15, 30)][1]))
    s.add(Or(start_hour + meeting_duration[0] > arthur_schedule[(16, 30)][0],
             end_hour < arthur_schedule[(16, 30)][1]))

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        m = s.model()
        # Print the solution
        print('SOLUTION:')
        print(f'Day: Monday')
        print(f'Start Time: {m[start_hour].as_string("%H:%M")}')
        print(f'End Time: {m[end_hour].as_string("%H:%M")}')
    else:
        print('No solution exists.')

# Define the existing schedules for each participant
michael_schedule = {(9, 30): (10, 30), (15, 0): (15, 30), (16, 0): (16, 30)}
eric_schedule = {(9, 0): (17, 0)}
arthur_schedule = {(9, 0): (12, 0), (13, 0): (15, 0), (15, 30): (16, 0), (16, 30): (17, 0)}

# Define the meeting duration
meeting_duration = (0, 30)

schedule_meeting(michael_schedule, eric_schedule, arthur_schedule, meeting_duration)