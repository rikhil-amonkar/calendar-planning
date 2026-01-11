from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, kyle_schedule, meeting_duration, work_start, work_end, excluded_days):
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    days_of_week = ["Monday", "Tuesday", "Wednesday"]
    available_days = [day for day in days_of_week if day not in excluded_days]
    
    for day in available_days:
        cheryl_busy = cheryl_schedule.get(day, [])
        kyle_busy = kyle_schedule.get(day, [])
        
        # Convert busy times to datetime objects
        cheryl_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in cheryl_busy]
        kyle_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in kyle_busy]
        
        # Initialize free time slots
        cheryl_free_times = []
        kyle_free_times = []
        
        # Calculate free time slots for Cheryl
        current_time = work_start
        for start, end in sorted(cheryl_busy_times):
            if current_time < start:
                cheryl_free_times.append((current_time, start))
            current_time = max(current_time, end)
        if current_time < work_end:
            cheryl_free_times.append((current_time, work_end))
        
        # Calculate free time slots for Kyle
        current_time = work_start
        for start, end in sorted(kyle_busy_times):
            if current_time < start:
                kyle_free_times.append((current_time, start))
            current_time = max(current_time, end)
        if current_time < work_end:
            kyle_free_times.append((current_time, work_end))
        
        # Find common free slots
        for ch_start, ch_end in cheryl_free_times:
            for ky_start, ky_end in kyle_free_times:
                common_start = max(ch_start, ky_start)
                common_end = min(ch_end, ky_end)
                if common_end - common_start >= meeting_duration:
                    return f"{common_start.strftime('%H:%M')}:{common_end.strftime('%H:%M')}", day
    
    return None, None

# Define the schedules
cheryl_schedule = {
    "Monday": [("9:00", "9:30"), ("11:30", "13:00"), ("15:30", "16:00")],
    "Tuesday": [("15:00", "15:30")]
}

kyle_schedule = {
    "Monday": [("9:00", "17:00")],
    "Tuesday": [("9:30", "17:00")],
    "Wednesday": [("9:00", "9:30"), ("10:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")]
}

# Meeting details
meeting_duration = 30  # in minutes
work_start = "9:00"
work_end = "17:00"
excluded_days = ["Wednesday"]

# Find the meeting time
time_range, day = find_meeting_time(cheryl_schedule, kyle_schedule, meeting_duration, work_start, work_end, excluded_days)
print(f"Meeting time: {time_range}, Day: {day}")