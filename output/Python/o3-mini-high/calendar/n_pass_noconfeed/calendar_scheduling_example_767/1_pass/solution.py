#!/usr/bin/env python3

def time_to_minutes(t):
    """Convert time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals.
       Each interval is a tuple (start, end) in minutes.
    """
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

# Define working hours and meeting duration in minutes.
start_day = time_to_minutes("09:00")
end_day = time_to_minutes("17:00")
meeting_duration = 60  # minutes

# Participant schedules: each day lists busy intervals as (start_time, end_time)
schedules = {
    "Martha": {
        "Monday": [("16:00", "17:00")],
        "Tuesday": [("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("14:00", "14:30")]
    },
    "Beverly": {
        "Monday": [("9:00", "13:30"), ("14:00", "17:00")],
        "Tuesday": [("9:00", "17:00")],
        "Wednesday": [("9:30", "15:30"), ("16:30", "17:00")]
    }
}

# Days available for the meeting.
days = ["Monday", "Tuesday", "Wednesday"]

meeting_found = False

for day in days:
    busy_intervals = []
    # Collect busy intervals for all participants on this day.
    for person in schedules:
        if day in schedules[person]:
            for interval in schedules[person][day]:
                start_str, end_str = interval
                busy_intervals.append((time_to_minutes(start_str), time_to_minutes(end_str)))
    
    # Merge overlapping busy intervals.
    merged_busy = merge_intervals(busy_intervals)
    
    # Compute free intervals within the working hours.
    free_intervals = []
    # Free time before the first busy interval.
    if merged_busy:
        if start_day < merged_busy[0][0]:
            free_intervals.append((start_day, merged_busy[0][0]))
        # Gaps between busy intervals.
        for i in range(len(merged_busy) - 1):
            if merged_busy[i][1] < merged_busy[i+1][0]:
                free_intervals.append((merged_busy[i][1], merged_busy[i+1][0]))
        # Free time after the last busy interval.
        if merged_busy[-1][1] < end_day:
            free_intervals.append((merged_busy[-1][1], end_day))
    else:
        free_intervals.append((start_day, end_day))
    
    # Look for a free interval that can accommodate the meeting.
    for free in free_intervals:
        free_start, free_end = free
        if free_end - free_start >= meeting_duration:
            meeting_start = free_start
            meeting_end = meeting_start + meeting_duration
            # Output the day and meeting time in the format HH:MM:HH:MM.
            print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            meeting_found = True
            break
    if meeting_found:
        break

if not meeting_found:
    print("No available meeting time found.")