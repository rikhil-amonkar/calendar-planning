from datetime import datetime, timedelta

def find_meeting_time(megan_schedule, daniel_schedule, meeting_duration, days):
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in days:
        start_time = datetime.strptime(f"{day} 09:00", "%A %H:%M")
        end_time = datetime.strptime(f"{day} 17:00", "%A %H:%M")
        
        current_time = start_time
        
        while current_time + meeting_duration <= end_time:
            if all(current_time not in busy and current_time + meeting_duration not in busy for busy in [megan_schedule[day], daniel_schedule[day]]):
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
            
            current_time += timedelta(minutes=30)  # Check every half hour

# Define the schedules
megan_schedule = {
    "Monday": [datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M"),
               datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 15:30", "%A %H:%M")],
    "Tuesday": [datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 09:30", "%A %H:%M"),
                datetime.strptime("Tuesday 12:00", "%A %H:%M"), datetime.strptime("Tuesday 12:30", "%A %H:%M"),
                datetime.strptime("Tuesday 16:00", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")],
    "Wednesday": [datetime.strptime("Wednesday 09:30", "%A %H:%M"), datetime.strptime("Wednesday 10:00", "%A %H:%M"),
                  datetime.strptime("Wednesday 10:30", "%A %H:%M"), datetime.strptime("Wednesday 11:30", "%A %H:%M"),
                  datetime.strptime("Wednesday 12:30", "%A %H:%M"), datetime.strptime("Wednesday 14:00", "%A %H:%M"),
                  datetime.strptime("Wednesday 16:00", "%A %H:%M"), datetime.strptime("Wednesday 16:30", "%A %H:%M")],
    "Thursday": [datetime.strptime("Thursday 13:30", "%A %H:%M"), datetime.strptime("Thursday 14:30", "%A %H:%M"),
                 datetime.strptime("Thursday 15:00", "%A %H:%M"), datetime.strptime("Thursday 15:30", "%A %H:%M")]
}

daniel_schedule = {
    "Monday": [datetime.strptime("Monday 10:00", "%A %H:%M"), datetime.strptime("Monday 11:30", "%A %H:%M"),
               datetime.strptime("Monday 12:30", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")],
    "Tuesday": [datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 10:00", "%A %H:%M"),
                datetime.strptime("Tuesday 10:30", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")],
    "Wednesday": [datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 10:00", "%A %H:%M"),
                  datetime.strptime("Wednesday 10:30", "%A %H:%M"), datetime.strptime("Wednesday 11:30", "%A %H:%M"),
                  datetime.strptime("Wednesday 12:00", "%A %H:%M"), datetime.strptime("Wednesday 17:00", "%A %H:%M")],
    "Thursday": [datetime.strptime("Thursday 09:00", "%A %H:%M"), datetime.strptime("Thursday 12:00", "%A %H:%M"),
                 datetime.strptime("Thursday 12:30", "%A %H:%M"), datetime.strptime("Thursday 14:30", "%A %H:%M"),
                 datetime.strptime("Thursday 15:00", "%A %H:%M"), datetime.strptime("Thursday 15:30", "%A %H:%M"),
                 datetime.strptime("Thursday 16:00", "%A %H:%M"), datetime.strptime("Thursday 17:00", "%A %H:%M")]
}

# Convert to intervals
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    megan_schedule[day] = [(megan_schedule[day][i], megan_schedule[day][i+1]) for i in range(0, len(megan_schedule[day]), 2)]
    daniel_schedule[day] = [(daniel_schedule[day][i], daniel_schedule[day][i+1]) for i in range(0, len(daniel_schedule[day]), 2)]

# Flatten the intervals into busy times
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    megan_busy_times = set()
    daniel_busy_times = set()
    for start, end in megan_schedule[day]:
        current = start
        while current < end:
            megan_busy_times.add(current)
            current += timedelta(minutes=30)
    for start, end in daniel_schedule[day]:
        current = start
        while current < end:
            daniel_busy_times.add(current)
            current += timedelta(minutes=30)
    megan_schedule[day] = megan_busy_times
    daniel_schedule[day] = daniel_busy_times

# Find the meeting time
meeting_time, meeting_day = find_meeting_time(megan_schedule, daniel_schedule, 1, ["Monday", "Tuesday", "Wednesday", "Thursday"])
print(f"{meeting_time}, {meeting_day}")