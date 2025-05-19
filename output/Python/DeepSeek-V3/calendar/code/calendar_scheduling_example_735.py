from datetime import datetime, timedelta

def find_earliest_meeting_time(participants_schedules, work_hours, meeting_duration, days):
    # Convert work hours to minutes since start of day
    work_start = int(work_hours[0].split(':')[0]) * 60 + int(work_hours[0].split(':')[1])
    work_end = int(work_hours[1].split(':')[0]) * 60 + int(work_hours[1].split(':')[1])
    
    # Preprocess blocked times into minutes since start of day for each day
    blocked_times = {}
    for day in days:
        blocked_times[day] = []
        for participant in participants_schedules:
            for block in participants_schedules[participant].get(day, []):
                start_time = block[0].split(':')
                end_time = block[1].split(':')
                start_min = int(start_time[0]) * 60 + int(start_time[1])
                end_min = int(end_time[0]) * 60 + int(end_time[1])
                blocked_times[day].append((start_min, end_min))
    
    # Check each day in order for the earliest available slot
    for day in days:
        # Merge and sort all blocked intervals for the day
        intervals = blocked_times[day]
        if not intervals:
            # No blocked times, entire work day is available
            return day, (work_hours[0], f"{int(work_start//60):02d}:{int(work_start%60):02d}", 
                         f"{int((work_start + meeting_duration)//60):02d}:{int((work_start + meeting_duration)%60):02d}")
        
        merged = []
        for start, end in sorted(intervals):
            if not merged:
                merged.append((start, end))
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1] = (last_start, max(end, last_end))
                else:
                    merged.append((start, end))
        
        # Check before first interval
        first_start, first_end = merged[0]
        if first_start - work_start >= meeting_duration:
            return day, (f"{int(work_start//60):02d}:{int(work_start%60):02d}", 
                          f"{int((work_start + meeting_duration)//60):02d}:{int((work_start + meeting_duration)%60):02d}")
        
        # Check between intervals
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            curr_start = merged[i][0]
            if curr_start - prev_end >= meeting_duration:
                return day, (f"{int(prev_end//60):02d}:{int(prev_end%60):02d}", 
                            f"{int((prev_end + meeting_duration)//60):02d}:{int((prev_end + meeting_duration)%60):02d}")
        
        # Check after last interval
        last_start, last_end = merged[-1]
        if work_end - last_end >= meeting_duration:
            return day, (f"{int(last_end//60):02d}:{int(last_end%60):02d}", 
                         f"{int((last_end + meeting_duration)//60):02d}:{int((last_end + meeting_duration)%60):02d}")
    
    return None, None

# Define the problem constraints
participants_schedules = {
    "Ronald": {
        "Monday": [("10:30", "11:00"), ("12:00", "12:30"), ("15:30", "16:00")],
        "Tuesday": [("9:00", "9:30"), ("12:00", "12:30"), ("15:30", "16:30")],
        "Wednesday": [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")],
    },
    "Amber": {
        "Monday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:30"), ("16:30", "17:00")],
        "Wednesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "13:30"), ("15:00", "15:30")],
    }
}

work_hours = ("9:00", "17:00")
meeting_duration = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday"]

# Find the earliest meeting time
day, time_range = find_earliest_meeting_time(participants_schedules, work_hours, meeting_duration, days)

# Output the result
if day and time_range:
    start_time, end_time = time_range
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")