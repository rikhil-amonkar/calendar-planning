from z3 import *

def schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration):
    # Define the day
    day = 'Monday'

    # Define the start and end times of the work hours
    start_time = 9
    end_time = 17

    # Define the meeting duration
    s = Optimize()

    # Define the meeting start time
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= start_time)
    s.add(meeting_start <= end_time - meeting_duration + 1)

    # Check if the meeting time conflicts with Kayla's schedule
    for start, end in kayla_schedule:
        conflict = (meeting_start >= start) + (meeting_start + meeting_duration <= end)
        s.add(conflict == 0)

    # Check if the meeting time conflicts with Rebecca's schedule
    for start, end in rebecca_schedule:
        conflict = (meeting_start >= start) + (meeting_start + meeting_duration <= end)
        s.add(conflict == 0)

    # Minimize the meeting start time
    s.minimize(meeting_start)

    # Solve the optimization problem
    if s.check() == sat:
        model = s.model()
        meeting_start_val = model[meeting_start].as_long()
        return f"SOLUTION:\nDay: {day}\nStart Time: {meeting_start_val:02d}:00\nEnd Time: {(meeting_start_val + meeting_duration - 1):02d}:00"
    else:
        return "No meeting time found"

# Example usage:
kayla_schedule = [(10 * 60 + 0, 10 * 60 + 30), (14 * 60 + 30, 16 * 60)]
rebecca_schedule = [(9 * 60, 13 * 60), (13 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)]
meeting_duration = 60

print(schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration))