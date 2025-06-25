from z3 import *

def schedule_meeting(bobby_schedule, michael_schedule, meeting_duration):
    # Create a Z3 solver
    s = Solver()

    # Define the day and time variables
    day = [Bool('day_%s' % i) for i in range(2)]
    start_time = [Int('start_time_%s' % i) for i in range(2)]
    end_time = [Int('end_time_%s' % i) for i in range(2)]

    # Add constraints for the day
    s.add(Or(day[0], day[1]))

    # Add constraints for the start and end times
    s.add(And(start_time[0] >= 9, start_time[0] <= 17))
    s.add(And(start_time[1] >= 9, start_time[1] <= 17))
    s.add(And(end_time[0] >= 9, end_time[0] <= 17))
    s.add(And(end_time[1] >= 9, end_time[1] <= 17))

    # Add constraints for the meeting duration
    s.add(And(start_time[0] + meeting_duration <= 17, start_time[1] + meeting_duration <= 17))

    # Add constraints for the busy times
    for i in range(2):
        for start, end in bobby_schedule:
            s.add(Or(Not(day[i]), start > end_time[i] or end < start_time[i]))
        for start, end in michael_schedule:
            s.add(Or(Not(day[i]), start > end_time[i] or end < start_time[i]))

    # Add constraints for the start and end times
    s.add(And(start_time[0] <= end_time[0], start_time[1] <= end_time[1]))

    # Add constraints for the meeting duration
    s.add(And(end_time[0] - start_time[0] == meeting_duration, end_time[1] - start_time[1] == meeting_duration))

    # Check if there's a solution
    if s.check() == sat:
        # Get the model
        m = s.model()

        # Print the solution
        day_to_meet = 'Monday' if m.evaluate(day[0]).as_bool() else 'Tuesday'
        start_time_to_meet = m.evaluate(start_time[0]).as_int()
        end_time_to_meet = m.evaluate(end_time[0]).as_int()

        print('SOLUTION:')
        print('Day: %s' % day_to_meet)
        print('Start Time: %02d:%02d' % (start_time_to_meet // 60, start_time_to_meet % 60))
        print('End Time: %02d:%02d' % (end_time_to_meet // 60, end_time_to_meet % 60))
    else:
        print('No solution found.')

# Define the existing schedules
bobby_schedule = [(14:30, 15:00), (9:00, 11:30), (12:00, 12:30), (13:00, 15:00), (15:30, 17:00)]
michael_schedule = [(9:00, 10:00), (10:30, 13:30), (14:00, 15:00), (15:30, 17:00), (9:00, 10:30), (11:00, 11:30), (12:00, 14:00), (15:00, 16:00), (16:30, 17:00)]

# Define the meeting duration
meeting_duration = 30

# Schedule the meeting
schedule_meeting(bobby_schedule, michael_schedule, meeting_duration)