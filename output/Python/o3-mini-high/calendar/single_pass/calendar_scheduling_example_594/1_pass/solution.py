def time_str_to_minutes(time_str):
    """Converts a time string HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time_str(minutes):
    """Converts minutes since midnight to a time string HH:MM."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    """Merges overlapping or contiguous intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last_start, last_end = merged[-1]
        current_start, current_end = current
        if current_start <= last_end:  # Overlapping or contiguous intervals.
            merged[-1] = (last_start, max(last_end, current_end))
        else:
            merged.append(current)
    return merged

def find_earliest_slot(working_start, working_end, merged_busy, meeting_duration):
    """
    Finds the earliest time slot within working hours that is free for at least the meeting_duration.
    Returns a tuple (start, end) in minutes if found, else None.
    """
    current_time = working_start

    # Check gap before the first busy interval.
    for busy_start, busy_end in merged_busy:
        if busy_start - current_time >= meeting_duration:
            return (current_time, current_time + meeting_duration)
        # Move the current time pointer forward if needed.
        current_time = max(current_time, busy_end)
    
    # Check after the last busy interval.
    if working_end - current_time >= meeting_duration:
        return (current_time, current_time + meeting_duration)
    return None

def main():
    # Meeting parameters
    meeting_duration = 30  # 30 minutes
    day = "Monday"
    working_start = time_str_to_minutes("09:00")
    working_end = time_str_to_minutes("17:00")
    
    # Busy schedules for each participant (times are in HH:MM format)
    adam_busy_times = [
        ("09:30", "10:00"),
        ("12:30", "13:00"),
        ("14:30", "15:00"),
        ("16:30", "17:00")
    ]
    
    roy_busy_times = [
        ("10:00", "11:00"),
        ("11:30", "13:00"),
        ("13:30", "14:30"),
        ("16:30", "17:00")
    ]
    
    # Convert busy times to intervals in minutes.
    busy_intervals = []
    for start_str, end_str in adam_busy_times + roy_busy_times:
        start = time_str_to_minutes(start_str)
        end = time_str_to_minutes(end_str)
        busy_intervals.append((start, end))
    
    # Merge overlapping busy intervals.
    merged_busy = merge_intervals(busy_intervals)
    
    # Find the earliest available time slot.
    slot = find_earliest_slot(working_start, working_end, merged_busy, meeting_duration)
    
    if slot:
        start_str = minutes_to_time_str(slot[0])
        end_str = minutes_to_time_str(slot[1])
        # Output format: HH:MM:HH:MM along with the day of the week.
        print(f"{day}: {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()