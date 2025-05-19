def minutes_to_time(minutes):
    """Convert minutes since midnight to a HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals. Assumes intervals is a list of (start, end) tuples."""
    if not intervals:
        return []
    # Sort intervals by start time
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        # if overlapping or contiguous, merge them
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_meeting_slot(busy_intervals, meeting_duration, work_start, work_end):
    """
    Given busy intervals, meeting duration (in minutes), work_start and work_end in minutes,
    find a free time slot that can fit the meeting.
    Returns (start, end) in minutes.
    """
    # Merge all busy intervals
    merged_busy = merge_intervals(busy_intervals)
    
    # Check for free time before the first busy interval after work_start.
    if work_start < merged_busy[0][0]:
        if merged_busy[0][0] - work_start >= meeting_duration:
            return (work_start, work_start + meeting_duration)
    
    # Check between busy intervals.
    for i in range(len(merged_busy) - 1):
        end_current = merged_busy[i][1]
        start_next = merged_busy[i+1][0]
        if start_next - end_current >= meeting_duration:
            return (end_current, end_current + meeting_duration)
    
    # Check after the last busy interval within work hours.
    if work_end - merged_busy[-1][1] >= meeting_duration:
        return (merged_busy[-1][1], merged_busy[-1][1] + meeting_duration)
    
    return None  # In case there is no available slot.

def main():
    # Define work hours in minutes from midnight: 9:00 to 17:00.
    work_start = 9 * 60   # 540 minutes (9:00)
    work_end = 17 * 60    # 1020 minutes (17:00)
    meeting_duration = 30  # 30 minutes
    
    # Busy intervals for each participant (in minutes since midnight)
    # Jacob: 13:30-14:00, 14:30-15:00
    busy_jacob = [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)]
    # Diana: 09:30-10:00, 11:30-12:00, 13:00-13:30, 16:00-16:30
    busy_diana = [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    # Adam: 09:30-10:30, 11:00-12:30, 15:30-16:00
    busy_adam = [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
    # Angela: 09:30-10:00, 10:30-12:00, 13:00-15:30, 16:00-16:30
    busy_angela = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 12 * 60), (13 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    # Dennis: 09:00-09:30, 10:30-11:30, 13:00-15:00, 16:30-17:00
    busy_dennis = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60 + 30), (13 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)]
    
    # Combine all busy intervals into one list.
    all_busy = busy_jacob + busy_diana + busy_adam + busy_angela + busy_dennis

    # To ensure only busy slots within work hours are considered,
    # we can clip intervals to within [work_start, work_end].
    clipped_busy = []
    for start, end in all_busy:
        if end <= work_start or start >= work_end:
            continue  # Skip intervals outside working hours.
        clipped_start = max(start, work_start)
        clipped_end = min(end, work_end)
        clipped_busy.append((clipped_start, clipped_end))
    
    # Find a free slot for the meeting
    meeting_slot = find_meeting_slot(clipped_busy, meeting_duration, work_start, work_end)
    
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        day = "Monday"
        # Output in the format HH:MM:HH:MM and day of the week.
        print(f"{day} {start_time}:{end_time}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()