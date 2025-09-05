def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    free_intervals = []
    current_start = work_start
    # Ensure the busy intervals are sorted
    busy_intervals.sort(key=lambda interval: interval[0])
    for b_start, b_end in busy_intervals:
        if b_start > current_start:
            free_intervals.append((current_start, min(b_start, work_end)))
        current_start = max(current_start, b_end)
        if current_start >= work_end:
            break
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """
    Return the intersection of two lists of intervals.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Compute intersection span
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list that finishes first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    # Define work hours for Monday (09:00 to 17:00)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # Meeting duration in minutes
    
    # Participant schedules in busy intervals (in minutes)
    # Denise is busy 12:00-12:30 and 15:30-16:00
    denise_busy = [
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ]
    
    # Angela has no meetings
    angela_busy = []
    
    # Natalie is busy 09:00-11:30, 12:00-13:00, 14:00-14:30, and 15:00-17:00
    natalie_busy = [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ]
    
    # Get free intervals for each participant within work hours
    denise_free = get_free_intervals(work_start, work_end, denise_busy)
    angela_free = get_free_intervals(work_start, work_end, angela_busy)
    natalie_free = get_free_intervals(work_start, work_end, natalie_busy)
    
    # Find common free intervals between all participants
    common_free = intersect_intervals(denise_free, angela_free)
    common_free = intersect_intervals(common_free, natalie_free)
    
    # Select the earliest interval that can accommodate the meeting duration
    meeting_slot = None
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        meeting_start, meeting_end = meeting_slot
        start_time_str = minutes_to_time(meeting_start)
        end_time_str = minutes_to_time(meeting_end)
        # Output the day and the time slot in the format HH:MM:HH:MM
        print("Monday")
        print(f"{start_time_str}:{end_time_str}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()