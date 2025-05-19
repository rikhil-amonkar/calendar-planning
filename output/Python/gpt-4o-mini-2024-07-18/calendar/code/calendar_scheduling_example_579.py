from datetime import datetime, timedelta

# Function to convert time in string format to datetime
def str_to_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Function to find meeting time
def find_meeting_time(participant1_schedule, participant2_schedule, meeting_duration, work_hours):
    work_start = str_to_time(work_hours[0])
    work_end = str_to_time(work_hours[1])
    meeting_duration = timedelta(minutes=meeting_duration)

    current_time = work_start
    while current_time + meeting_duration <= work_end:
        meeting_start = current_time
        meeting_end = current_time + meeting_duration

        # Check if the meeting conflicts with participant 1's schedule
        conflict1 = any(start < meeting_end and end > meeting_start for start, end in participant1_schedule)
        # Check if the meeting conflicts with participant 2's schedule
        conflict2 = any(start < meeting_end and end > meeting_start for start, end in participant2_schedule)

        if not conflict1 and not conflict2:
            return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} on Monday"

        current_time += timedelta(minutes=30)  # Increment time by 30 min

    return "No available time found"

# Existing schedules for both participants
christine_schedule = [(str_to_time("11:00"), str_to_time("11:30")),
                      (str_to_time("15:00"), str_to_time("15:30"))]

helen_schedule = [(str_to_time("9:30"), str_to_time("10:30")),
                  (str_to_time("11:00"), str_to_time("11:30")),
                  (str_to_time("12:00"), str_to_time("12:30")),
                  (str_to_time("13:30"), str_to_time("16:00")),
                  (str_to_time("16:30"), str_to_time("17:00"))]

# Define meeting duration and work hours
meeting_duration = 30  # in minutes
work_hours = ("09:00", "17:00")

# Find suitable meeting time
meeting_time = find_meeting_time(christine_schedule, helen_schedule, meeting_duration, work_hours)
print(meeting_time)