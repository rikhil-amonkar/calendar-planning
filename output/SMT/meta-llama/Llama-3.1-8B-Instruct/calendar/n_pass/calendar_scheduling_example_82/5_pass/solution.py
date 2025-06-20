from z3 import *

def schedule_meeting(michael_schedule, eric_schedule, arthur_schedule, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define the day of the meeting
    day = Int('day')
    s.add(day == 1)  # Meeting is on Monday

    # Define the start and end time of the meeting
    start_hour = Int('start_hour')
    s.add(And(9 <= start_hour, start_hour + meeting_duration[0] <= 17))  # Start time is between 9:00 and 16:00

    # Add constraints for each participant
    s.add(Implies(start_hour + meeting_duration[0] < 10, start_hour + meeting_duration[0] > michael_schedule[(9, 30)][0]))
    s.add(Implies(start_hour + meeting_duration[0] < 15.5, start_hour + meeting_duration[0] > michael_schedule[(15, 0)][0]))
    s.add(Implies(start_hour + meeting_duration[0] < 16.5, start_hour + meeting_duration[0] > michael_schedule[(16, 0)][0]))
    s.add(Implies(start_hour + meeting_duration[0] < 12.5, start_hour + meeting_duration[0] > arthur_schedule[(9, 0)][0]))
    s.add(Implies(start_hour + meeting_duration[0] < 13.5, start_hour + meeting_duration[0] > arthur_schedule[(13, 0)][0]))
    s.add(Implies(start_hour + meeting_duration[0] < 16, start_hour + meeting_duration[0] > arthur_schedule[(15, 30)][0]))
    s.add(Implies(start_hour + meeting_duration[0] < 17, start_hour + meeting_duration[0] > arthur_schedule[(16, 30)][0]))

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        m = s.model()
        # Print the solution
        print('SOLUTION:')
        print(f'Day: Monday')
        print(f'Start Time: {m[start_hour].as_string("%H:%M")}')
        print(f'End Time: {(m[start_hour] + meeting_duration[0]).as_string("%H:%M")}')
    else:
        print('No solution exists.')

# Define the existing schedules for each participant
michael_schedule = {(9, 30): (10, 30), (15, 0): (15, 30), (16, 0): (16, 30)}
eric_schedule = {(9, 0): (17, 0)}
arthur_schedule = {(9, 0): (12, 0), (13, 0): (15, 0), (15, 30): (16, 0), (16, 30): (17, 0)}

# Define the meeting duration
meeting_duration = (30, 30)

schedule_meeting(michael_schedule, eric_schedule, arthur_schedule, meeting_duration)