from datetime import datetime, timedelta

def find_meeting_time(participant_schedules, meeting_duration, available_days):
    work_hours = (datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    
    # Store availability for each day
    availability = {}
    
    for day in available_days:
        availability[day] = []
        for start, end in participant_schedules[day]:
            available_start = max(work_hours[0], start)
            available_end = min(work_hours[1], end)
            if available_start < available_end:
                availability[day].append((available_start, available_end))
    
    # Check for times in each day
    for day, times in availability.items():
        merged_times = merge_intervals(times)

        for start, end in merged_times:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                if meeting_end <= end:
                    return day, meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M")
    
    return None

def merge_intervals(intervals):
    if not intervals:
        return []
    
    # Sort intervals based on the starting time
    intervals.sort(key=lambda x: x[0])
    
    merged = []
    current_start, current_end = intervals[0]
    
    for start, end in intervals[1:]:
        if start <= current_end:  # Overlapping intervals
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
            
    merged.append((current_start, current_end))
    return merged

# Participant schedules
schedules = {
    "Monday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Wednesday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

meeting_time = find_meeting_time(schedules, timedelta(hours=1), ["Monday", "Tuesday", "Wednesday"])
if meeting_time:
    print(f"{meeting_time[1]}:{meeting_time[2]}:{meeting_time[0]}")