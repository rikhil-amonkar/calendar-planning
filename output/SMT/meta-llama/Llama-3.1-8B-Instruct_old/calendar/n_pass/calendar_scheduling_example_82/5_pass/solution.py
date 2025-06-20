from z3 import *

def schedule_meeting(michael_schedule, eric_schedule, arthur_schedule, meeting_duration):
    # Define the day to meet
    day = 'Monday'

    # Define the start and end time of work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Create Z3 variables for start time
    start = Int('start')
    with Solver() as s:
        # Add constraints for each participant's schedule
        for time in michael_schedule:
            s.add(And(start + 60 >= time[0], start + 60 <= time[1]))
        for time in eric_schedule:
            s.add(And(start + 60 >= time[0], start + 60 <= time[1]))
        for time in arthur_schedule:
            s.add(And(start + 60 >= time[0], start + 60 <= time[1]))
        
        # Add constraints for meeting duration
        s.add(And(start >= 9 * 60, start + 60 + meeting_duration <= 17 * 60))
        s.add(Implies(start + 60 >= 9 * 60 + 30, start + 60 + meeting_duration > 12 * 60))
        s.add(Implies(start + 60 >= 13 * 60, start + 60 + meeting_duration > 15 * 60))
        s.add(Implies(start + 60 >= 15 * 60 + 30, start + 60 + meeting_duration > 16 * 60))
        s.add(Implies(start + 60 >= 16 * 60 + 30, start + 60 + meeting_duration > 17 * 60))

        # Check if there's a solution
        if s.check() == sat:
            model = s.model()
            start_time = model[start].as_long() // 60
            end_time = (model[start].as_long() // 60) + meeting_duration
            return f'SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:{start_time % 60:02d}\nEnd Time: {end_time:02d}:{end_time % 60:02d}'
        else:
            return 'No solution found'

# Example usage
michael_schedule = [(9 * 60 + 30, 10 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
eric_schedule = []
arthur_schedule = [(9 * 60, 12 * 60), (13 * 60, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
meeting_duration = 30

print(schedule_meeting(michael_schedule, eric_schedule, arthur_schedule, meeting_duration))