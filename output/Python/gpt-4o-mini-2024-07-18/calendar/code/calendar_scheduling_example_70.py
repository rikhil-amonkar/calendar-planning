from datetime import datetime, timedelta

# Participants' schedules in the time range for Monday
denise_schedule = [
    (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
    (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))
]

angela_schedule = []  # No meetings for Angela

natalie_schedule = [
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
    (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
    (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
    (datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))
]

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Define work hours
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')

# Function to find the earliest meeting time
def find_meeting_time(denise_schedule, angela_schedule, natalie_schedule, work_start, work_end, meeting_duration):
    all_schedules = denise_schedule + angela_schedule + natalie_schedule
    all_schedules.sort()  # Sort all schedules by start time

    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if all(not (start < current_time + meeting_duration and end > current_time) for start, end in all_schedules):
            return current_time.strftime('%H:%M:%H:%M'), 'Monday'
        current_time += timedelta(minutes=30)  # Increment time by 30 minutes

    return None, None

# Get the proposed meeting time
proposed_time, day_of_week = find_meeting_time(denise_schedule, angela_schedule, natalie_schedule, work_start, work_end, meeting_duration)

# Final output
if proposed_time:
    print(f"{proposed_time} {day_of_week}")