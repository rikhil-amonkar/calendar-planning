from z3 import *

def schedule_meeting(jeffrey_available, harold_available, meeting_duration, day, harold_preferences):
    # Create Z3 solver
    s = Solver()

    # Define variables
    day_var = Int('day')
    start_time_var = Int('start_time')
    end_time_var = Int('end_time')

    # Define constraints
    s.add(day_var == day)
    s.add(0 <= start_time_var)
    s.add(start_time_var < 12) # assuming 12 hours in a day
    s.add(end_time_var == start_time_var + meeting_duration * 60) # convert meeting duration from hours to minutes

    # Ensure meeting does not conflict with harold's blocked time
    for i in range(len(harold_available)):
        s.add(Or(start_time_var + meeting_duration * 60 > harold_available[i][0] * 60, 
                 start_time_var * 60 >= harold_available[i][1] * 60))

    # Ensure meeting does not conflict with harold's preferences
    for i in range(len(harold_preferences)):
        s.add(Or(start_time_var + meeting_duration * 60 > harold_preferences[i][0] * 60, 
                 start_time_var * 60 >= harold_preferences[i][1] * 60))

    # Ensure meeting does not conflict with jeffrey's available time
    for i in range(len(jeffrey_available)):
        s.add(Or(start_time_var + meeting_duration * 60 > jeffrey_available[i][0] * 60, 
                 start_time_var * 60 >= jeffrey_available[i][1] * 60))

    # Check if a solution exists
    if s.check() == sat:
        # Extract solution
        model = s.model()
        day_val = model[day_var].as_long()
        start_time_val = model[start_time_var].as_long()
        end_time_val = model[end_time_var].as_long()

        # Print solution
        print('SOLUTION:')
        print(f'Day: {["Monday", "Tuesday"][day_val-1]}')
        print(f'Start Time: {start_time_val:02d}:00')
        print(f'End Time: {(start_time_val + int(meeting_duration * 60) // 60):02d}:00')
    else:
        # Try alternative day
        s.reset()
        s.add(day_var == 2)
        if s.check() == sat:
            # Extract solution
            model = s.model()
            day_val = model[day_var].as_long()
            start_time_val = model[start_time_var].as_long()
            end_time_val = model[end_time_var].as_long()

            # Print solution
            print('SOLUTION:')
            print(f'Day: {["Monday", "Tuesday"][day_val-1]}')
            print(f'Start Time: {start_time_val:02d}:00')
            print(f'End Time: {(start_time_val + int(meeting_duration * 60) // 60):02d}:00')
        else:
            print('No solution exists')

# Example usage
jeffrey_available = [(0, 24)]  # Jeffrey is free the entire week
harold_available = [(9, 10), (10.5, 17), (9, 9.5), (9.5, 10.5), (10.5, 11.5), (11.5, 12.5), (12.5, 13.5), (13.5, 14.5), (14.5, 15.5), (15.5, 16), (16, 17)]  # Harold's blocked calendar
meeting_duration = 0.5  # Half an hour
day = 1  # Monday
harold_preferences = [(9, 9.5), (9.5, 10.5), (10.5, 11.5), (11.5, 12.5), (12.5, 13.5), (13.5, 14.5), (14.5, 15.5), (15.5, 16), (16, 17)]  # Harold's preferences

schedule_meeting(jeffrey_available, harold_available, meeting_duration, day, harold_preferences)