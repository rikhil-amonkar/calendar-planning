from datetime import datetime, timedelta

# Define the schedules for Eugene and Eric
eugene_schedule = {
    'Monday': [(10, 11), (11, 12), (13, 14), (14, 15), (16, 16.5)],
    'Tuesday': [],
    'Wednesday': [(9, 9.5), (11, 11.5), (12, 12.5), (13, 15)],
    'Thursday': [(9, 10), (11, 12.5)],
    'Friday': [(10, 10.5), (12, 12.5), (13, 13.5)]
}

eric_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11.5), (12, 14), (14, 16.5)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 11), (11, 17)]
}

# Eric's preference to avoid meetings on Wednesday
eric_preferred_days = ['Monday', 'Tuesday', 'Thursday', 'Friday']

# Meeting duration
meeting_duration = timedelta(hours=0.5)

# Function to find a suitable time for the meeting
def find_meeting_time(eugene_schedule, eric_schedule, eric_preferred_days, meeting_duration):
    for day in eric_preferred_days:
        available_times = []
        for start, end in eugene_schedule[day]:
            available_times.append((start, end))
        
        for start, end in eric_schedule[day]:
            for i, (eugene_start, eugene_end) in enumerate(available_times):
                if eugene_start < start < eugene_end or eugene_start < end < eugene_end or start < eugene_start < end:
                    available_times.pop(i)
        
        for start, end in available_times:
            if start + meeting_duration <= end:
                start_time = datetime(1900, 1, 1, int(start), int((start % 1) * 60))
                end_time = start_time + meeting_duration
                return f"{day}, {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}"
    
    return "No suitable time found"

# Find and print the meeting time
print(find_meeting_time(eugene_schedule, eric_schedule, eric_preferred_days, timedelta(hours=0.5)))