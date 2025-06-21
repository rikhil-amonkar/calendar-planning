from z3 import *

def schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, preferred_time=None, constraints=None):
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end time of the work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the meeting duration in minutes
    meeting_duration_minutes = meeting_duration * 60

    # Create a list of time slots
    time_slots = [i for i in range(start_time, end_time) if i not in jack_schedule and i not in charlotte_schedule]

    # If a preferred time is given, try to schedule the meeting at that time
    if preferred_time:
        preferred_time_minutes = preferred_time * 60
        if preferred_time_minutes in time_slots:
            start_time_minutes = preferred_time_minutes
            end_time_minutes = start_time_minutes + meeting_duration_minutes
        else:
            # If the preferred time is not available, try to schedule the meeting as close to the preferred time as possible
            closest_time = min(time_slots, key=lambda x:abs(x-preferred_time_minutes))
            start_time_minutes = closest_time
            end_time_minutes = start_time_minutes + meeting_duration_minutes
    else:
        # If no preferred time is given, try to schedule the meeting at the earliest available time
        start_time_minutes = min(time_slots)
        end_time_minutes = start_time_minutes + meeting_duration_minutes

    # Ensure that Jack doesn't have any meetings after 12:30
    if 12 * 60 + 30 in jack_schedule:
        jack_schedule_after_12_30 = [i for i in jack_schedule if i > 12 * 60 + 30]
        if start_time_minutes > max(jack_schedule_after_12_30):
            return 'No solution found'

    # Ensure that the meeting duration is not too long
    if end_time_minutes - start_time_minutes > meeting_duration_minutes:
        return 'No solution found'

    return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_minutes // 60}:{start_time_minutes % 60:02d}\nEnd Time: {end_time_minutes // 60}:{end_time_minutes % 60:02d}'

# Example usage:
jack_schedule = [9 * 60 + 30, 10 * 60 + 30, 11 * 60, 11 * 60 + 30, 12 * 60 + 30, 14 * 60, 14 * 60 + 30, 16 * 60, 16 * 60 + 30]
charlotte_schedule = [9 * 60 + 30, 10 * 60, 10 * 60 + 30, 12 * 60, 12 * 60 + 30, 14 * 60, 14 * 60 + 30, 16 * 60]
meeting_duration = 0.5
preferred_time = 12
print(schedule_meeting(jack_schedule, charlotte_schedule, meeting_duration, preferred_time))