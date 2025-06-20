from z3 import *

def schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration):
    # Define the day
    day = 'Monday'

    # Define the start and end times of the work hours
    start_time = 9
    end_time = 17

    # Define the meeting duration
    meeting_start = start_time
    while meeting_start < end_time - meeting_duration + 1:
        # Check if the meeting time conflicts with Kayla's schedule
        if (meeting_start >= 10 and meeting_start < 10 + meeting_duration) or \
           (meeting_start + meeting_duration > 10 and meeting_start + meeting_duration <= 10 + 30) or \
           (meeting_start + meeting_duration > 14 * 60 + 30 and meeting_start + meeting_duration <= 16 * 60):
            meeting_start += 1
            continue

        # Check if the meeting time conflicts with Rebecca's schedule
        if (meeting_start >= 9 and meeting_start < 13) or \
           (meeting_start >= 13 * 60 + 30 and meeting_start < 15 * 60) or \
           (meeting_start >= 15 * 60 + 30 and meeting_start < 16 * 60):
            meeting_start += 1
            continue

        # If the meeting time does not conflict with either Kayla's or Rebecca's schedule, return the meeting time
        return f"SOLUTION:\nDay: {day}\nStart Time: {meeting_start:02d}:00\nEnd Time: {(meeting_start + meeting_duration - 1):02d}:00"

    # If no meeting time is found, return an error message
    return "No meeting time found"

# Example usage:
kayla_schedule = [(10, 10 + 30), (14 * 60 + 30, 16 * 60)]
rebecca_schedule = [(9, 13), (13 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)]
meeting_duration = 60

print(schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration))