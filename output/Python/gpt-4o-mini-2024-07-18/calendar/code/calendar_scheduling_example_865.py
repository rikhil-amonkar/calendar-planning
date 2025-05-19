# Define participants' schedules
megan_schedule = {
    'Monday': [(9, 0, 13, 0), (13, 30, 14, 0), (14, 0, 15, 30), (15, 30, 17, 0)],
    'Tuesday': [(9, 0, 9, 30), (9, 30, 12, 0), (12, 30, 16, 0), (16, 0, 17, 0)],
    'Wednesday': [(9, 0, 9, 30), (9, 30, 10, 0), (10, 0, 10, 30), (10, 30, 11, 30), 
                  (11, 30, 12, 30), (12, 30, 14, 0), (14, 0, 16, 0), (16, 0, 16, 30)],
    'Thursday': [(9, 0, 13, 30), (13, 30, 15, 0), (15, 0, 15, 30), (15, 30, 17, 0)]
}

daniel_schedule = {
    'Monday': [(9, 0, 10, 0), (10, 0, 11, 30), (11, 30, 12, 30), (12, 30, 15, 0)],
    'Tuesday': [(9, 0, 10, 0), (10, 0, 10, 30), (10, 30, 17, 0)],
    'Wednesday': [(9, 0, 9, 0), (9, 0, 10, 0), (10, 0, 10, 30), (10, 30, 11, 30), 
                  (11, 30, 12, 0), (12, 0, 17, 0)],
    'Thursday': [(9, 0, 12, 0), (12, 0, 12, 30), (12, 30, 14, 30), (14, 30, 15, 0),
                 (15, 0, 15, 30), (15, 30, 17, 0)]
}

# Function to convert time to minutes
def time_to_minutes(hour, minute):
    return hour * 60 + minute

# Find available meeting slots
def find_meeting_time(schedule_a, schedule_b, duration=60):
    for day in schedule_a.keys():
        busy_times = schedule_a[day] + schedule_b[day]
        busy_times.sort()
        
        # Flatten the busy times into a free time schedule
        free_times = []
        last_end = 9 * 60  # Start at 9:00
        
        for start, end in busy_times:
            if last_end < time_to_minutes(start, 0):
                free_times.append((last_end, time_to_minutes(start, 0)))
            last_end = max(last_end, time_to_minutes(end, 0))
        
        # End at 17:00
        if last_end < 17 * 60:
            free_times.append((last_end, 17 * 60)) 
        
        # Check for a time slot that fits the meeting duration
        for start, end in free_times:
            if end - start >= duration:
                return day, start, start + duration
            
    return None

# Find the earliest available time slot for Megan and Daniel
day, start_time, end_time = find_meeting_time(megan_schedule, daniel_schedule)

# Convert back to hours and minutes
start_hour = start_time // 60
start_minute = start_time % 60
end_hour = end_time // 60
end_minute = end_time % 60

# Output the proposed time
print(f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02}")
print(day)