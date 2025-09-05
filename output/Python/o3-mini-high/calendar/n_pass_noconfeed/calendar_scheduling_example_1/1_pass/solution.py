def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # busy_intervals is a list of tuples (start, end) in minutes.
    free = []
    current = work_start
    for start, end in sorted(busy_intervals):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2, meeting_duration):
    common = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start >= meeting_duration:
                common.append((start, end))
    return common

def main():
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end   = time_to_minutes("17:00")
    day = "Monday"
    
    # Busy times for each participant (as strings)
    raymond_busy_str = [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "15:30")]
    billy_busy_str   = [("10:00", "10:30"), ("12:00", "13:00"), ("16:30", "17:00")]
    donald_busy_str  = [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "13:00"), ("14:00", "14:30"), ("16:00", "17:00")]
    
    # Convert busy times to minutes
    raymond_busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in raymond_busy_str]
    billy_busy   = [(time_to_minutes(s), time_to_minutes(e)) for s, e in billy_busy_str]
    donald_busy  = [(time_to_minutes(s), time_to_minutes(e)) for s, e in donald_busy_str]
    
    # Get free intervals for each participant within work hours
    raymond_free = get_free_intervals(raymond_busy, work_start, work_end)
    billy_free   = get_free_intervals(billy_busy, work_start, work_end)
    donald_free  = get_free_intervals(donald_busy, work_start, work_end)
    
    # Calculate the common free intervals across all participants.
    common_free = intersect_intervals(raymond_free, billy_free, meeting_duration)
    common_free = intersect_intervals(common_free, donald_free, meeting_duration)
    
    # Billy prefers not to have meetings after 15:00 (i.e., 15:00 in minutes)
    billy_pref_end = time_to_minutes("15:00")
    meeting_start = None
    meeting_end = None

    # Choose the earliest slot that can finish by 15:00 if possible.
    for start, end in sorted(common_free, key=lambda x: x[0]):
        if start + meeting_duration <= end:
            if start + meeting_duration <= billy_pref_end:
                meeting_start = start
                meeting_end = start + meeting_duration
                break

    # If no slot meets the preference, then choose the earliest overall.
    if meeting_start is None:
        for start, end in sorted(common_free, key=lambda x: x[0]):
            if start + meeting_duration <= end:
                meeting_start = start
                meeting_end = start + meeting_duration
                break

    if meeting_start is not None:
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        # Output the day and time slot in the required format: HH:MM:HH:MM
        print(day)
        print(f"{{{start_str}:{end_str}}}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()