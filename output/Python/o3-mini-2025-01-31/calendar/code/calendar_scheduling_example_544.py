from datetime import datetime, timedelta

def time_from_str(timestr):
    return datetime.strptime(timestr, "%H:%M")

def str_from_time(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_slot():
    # Meeting and work parameters
    meeting_duration = timedelta(minutes=30)
    work_day = "Monday"
    work_start = time_from_str("09:00")
    work_end = time_from_str("17:00")
    
    # Albert's calendar blocks (only Monday, in work hours)
    # Note: Although one block is at 15:00-16:30, Albert cannot meet after 11:00.
    # Thus, we only consider his blocks before 11:00 and adjust work_end accordingly.
    albert_blocks = [
        (time_from_str("09:00"), time_from_str("10:00")),
        (time_from_str("10:30"), time_from_str("12:00")),  # This block covers after the allowed meeting time
        (time_from_str("15:00"), time_from_str("16:30"))
    ]
    # Constraint: Albert cannot meet after 11:00.
    latest_meeting_end = time_from_str("11:00")
    # Adjust effective work end for Albert
    effective_work_end = min(work_end, latest_meeting_end)
    
    # Deborah is free all day, so we only consider Albert's schedule.
    # For simplicity, let's calculate Albert's free intervals in [work_start, effective_work_end].
    free_intervals = []
    current = work_start

    # We only consider the blocks that affect the interval until effective_work_end.
    for block_start, block_end in albert_blocks:
        # Skip blocks that start after effective_work_end, as they don't affect scheduling.
        if block_start >= effective_work_end:
            continue
        # If there's free time between current time and the block start, add it.
        if current < block_start:
            free_interval_end = min(block_start, effective_work_end)
            if free_interval_end - current >= meeting_duration:
                free_intervals.append((current, free_interval_end))
        # Move current to the later of block_end or current.
        if block_end > current:
            current = block_end
        # If current passed effective_work_end, break early.
        if current >= effective_work_end:
            break

    # Check if there is free time after the last block until effective_work_end.
    if current < effective_work_end and (effective_work_end - current) >= meeting_duration:
        free_intervals.append((current, effective_work_end))
    
    # Now, pick the first free interval that can accommodate the meeting.
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            return work_day, meeting_start, meeting_end

    return None, None, None

if __name__ == "__main__":
    day, start_time, end_time = find_meeting_slot()
    if day is None:
        print("No available slot found.")
    else:
        # Format output as HH:MM:HH:MM and print day as well.
        print(f"{day}, {str_from_time(start_time)}:{str_from_time(end_time)}")