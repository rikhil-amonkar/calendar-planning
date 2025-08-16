from datetime import datetime, timedelta

def find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration, work_start, work_end, days):
    meeting_duration = timedelta(hours=meeting_duration)
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")

    for day in days:
        jesse_busy = jesse_schedule[day]
        lawrence_busy = lawrence_schedule[day]
        
        # Convert busy times to datetime objects
        jesse_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in jesse_busy]
        lawrence_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in lawrence_busy]
        
        # Combine and sort all busy times
        all_busy_times = sorted(jesse_busy_times + lawrence_busy_times)
        
        # Initialize start time as work start
        current_time = work_start
        
        for start, end in all_busy_times:
            # Check if there's a gap between current time and next busy period
            if start > current_time:
                potential_end = current_time + meeting_duration
                if potential_end <= end and potential_end <= work_end:
                    return f"{current_time.strftime('%H:%M')}:{potential_end.strftime('%H:%M')}", day
            
            # Move current time to the end of the current busy period
            current_time = max(current_time, end)
        
        # Check if there's time left at the end of the day
        if work_end - current_time >= meeting_duration:
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
    
    return None, None

# Define schedules
jesse_schedule = {
    "Monday": [("13:30", "14:00"), ("14:30", "15:00")],
    "Tuesday": [("9:00", "9:30"), ("13:00", "13:30"), ("14:00", "15:00")]
}

lawrence_schedule = {
    "Monday": [("9:00", "17:00")],
    "Tuesday": [("9:30", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "16:30")]
}

# Meeting details
meeting_duration = 0.5  # Half an hour
work_start = "9:00"
work_end = "17:00"
days = ["Monday", "Tuesday"]

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration, work_start, work_end, days)

# Output the result
print(f"{meeting_time}, {meeting_day}")