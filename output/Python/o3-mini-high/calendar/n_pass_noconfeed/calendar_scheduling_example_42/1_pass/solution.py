def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    # Sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        # Merge if intervals overlap or touch
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_meeting_slot(busy_intervals, work_start, work_end, meeting_duration):
    # Merge all busy intervals
    merged_busy = merge_intervals(busy_intervals)
    
    free_intervals = []
    current_time = work_start
    for block in merged_busy:
        start, end = block
        if start > current_time:
            free_intervals.append((current_time, start))
        current_time = max(current_time, end)
    # Check gap after the last busy interval
    if current_time < work_end:
        free_intervals.append((current_time, work_end))
    
    # Find a free interval that can accommodate the meeting
    for free_start, free_end in free_intervals:
        if free_end - free_start >= meeting_duration:
            return free_start, free_start + meeting_duration
    return None

def main():
    # Define work hours for Monday: from 09:00 (540 minutes) to 17:00 (1020 minutes)
    work_start = 9 * 60      # 540 minutes
    work_end = 17 * 60       # 1020 minutes
    meeting_duration = 60    # Meeting duration is 60 minutes
    
    # Busy slots for each participant (times in minutes from midnight)
    # Julie's busy time: 09:00-09:30, 11:00-11:30, 12:00-12:30, 13:30-14:00, 16:00-17:00
    julie_busy = [
        (9 * 60, 9 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60, 12 * 60 + 30),
        (13 * 60 + 30, 14 * 60),
        (16 * 60, 17 * 60)
    ]
    
    # Sean's busy time: 09:00-09:30, 13:00-13:30, 15:00-15:30, 16:00-16:30
    sean_busy = [
        (9 * 60, 9 * 60 + 30),
        (13 * 60, 13 * 60 + 30),
        (15 * 60, 15 * 60 + 30),
        (16 * 60, 16 * 60 + 30)
    ]
    
    # Lori's busy time: 10:00-10:30, 11:00-13:00, 15:30-17:00
    lori_busy = [
        (10 * 60, 10 * 60 + 30),
        (11 * 60, 13 * 60),
        (15 * 60 + 30, 17 * 60)
    ]
    
    # Combine all busy intervals
    all_busy = julie_busy + sean_busy + lori_busy
    
    meeting_slot = find_meeting_slot(all_busy, work_start, work_end, meeting_duration)
    if meeting_slot:
        start, end = meeting_slot
        start_str = minutes_to_str(start)
        end_str = minutes_to_str(end)
        day = "Monday"
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()