from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Initialize available times as the full work day
    available_times = [(work_start, work_end)]
    
    # Iterate over each participant's schedule and remove busy times
    for person, busy_times in participants.items():
        new_available_times = []
        for start, end in available_times:
            remaining_start, remaining_end = start, end
            for busy_start, busy_end in busy_times:
                busy_start = datetime.strptime(busy_start, "%H:%M")
                busy_end = datetime.strptime(busy_end, "%H:%M")
                
                if busy_start <= remaining_start < busy_end:
                    remaining_start = busy_end
                elif remaining_start < busy_start < remaining_end:
                    new_available_times.append((remaining_start, busy_start))
                    remaining_start = busy_end
            
            if remaining_start < remaining_end:
                new_available_times.append((remaining_start, remaining_end))
        
        available_times = new_available_times
    
    # Find the first available slot that fits the meeting duration
    for start, end in available_times:
        if end - start >= meeting_duration:
            meeting_start = start.strftime("%H:%M")
            meeting_end = (start + meeting_duration).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end}", "Monday"
    
    return None, None

# Define participants' schedules
participants = {
    "Patrick": [("9:00", "9:30"), ("10:00", "10:30"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Kayla": [("12:30", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    "Carl": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "17:00")],
    "Christian": [("9:00", "12:30"), ("13:00", "14:00"), ("14:30", "17:00")]
}

# Meeting parameters
meeting_duration = 30
work_start = "9:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"{meeting_time}, {day}")