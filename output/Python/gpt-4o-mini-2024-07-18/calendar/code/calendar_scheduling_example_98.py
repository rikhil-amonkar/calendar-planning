from datetime import datetime, timedelta

# Define the working hours
working_hours_start = datetime.strptime("09:00", "%H:%M")
working_hours_end = datetime.strptime("17:00", "%H:%M")

# Meeting duration in minutes
meeting_duration = 30

# Existing schedules (busy times)
juan_busy_times = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                   (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]

marilyn_busy_times = [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                      (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"))]

ronald_busy_times = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                     (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                     (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                     (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

# Merge all busy times into a single list
busy_times = juan_busy_times + marilyn_busy_times + ronald_busy_times

# Function to find a suitable time slot
def find_meeting_time(busy_times, duration, start, end):
    # Sort busy times
    busy_times.sort()
    
    # Check available time slots
    current_time = start

    for busy_start, busy_end in busy_times:
        # Check if there's enough time before the next busy time
        if current_time + timedelta(minutes=duration) <= busy_start:
            return current_time, current_time + timedelta(minutes=duration)
        
        # Move the current time to the end of the busy time
        current_time = max(current_time, busy_end)
    
    # Check if there's time after all busy schedules until the end of the workday
    if current_time + timedelta(minutes=duration) <= end:
        return current_time, current_time + timedelta(minutes=duration)

# Find a meeting time
meeting_start, meeting_end = find_meeting_time(busy_times, meeting_duration, working_hours_start, working_hours_end)

# Output the result in specified format
meeting_time_range = f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}"
day_of_week = "Monday"

print(meeting_time_range)
print(day_of_week)