from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime('09:00', '%H:%M')
work_end = datetime.strptime('17:00', '%H:%M')
meeting_duration = timedelta(hours=1)

# Existing schedules for each participant
schedules = {
    'Stephanie': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                  (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Cheryl': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
               (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
               (datetime.strptime('16:30', '%H:%M'), work_end)],
    'Bradley': [(datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
                (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                (datetime.strptime('15:30', '%H:%M'), work_end)],
    'Steven': [(work_start, datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
               (datetime.strptime('14:30', '%H:%M'), work_end)]
}

# Function to find a suitable time for the meeting
def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    free_times = []
    current_start = work_start

    while current_start + meeting_duration <= work_end:
        current_end = current_start + meeting_duration
        if all(not (current_start < end and current_end > start) for times in schedules.values() for start, end in times):
            free_times.append((current_start, current_end))
        current_start += timedelta(minutes=30)  # Check every 30 minutes

    return free_times

# Find free times and select the first available
available_times = find_meeting_time(schedules, meeting_duration, work_start, work_end)

if available_times:
    proposed_time = available_times[0]
    start_time_str = proposed_time[0].strftime('%H:%M')
    end_time_str = proposed_time[1].strftime('%H:%M')
    day_of_week = 'Monday'
    print(f"{start_time_str}:{end_time_str}")
    print(day_of_week)
else:
    print("No available time found.")