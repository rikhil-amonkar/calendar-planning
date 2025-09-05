def parse_time(t):
    """Converts HH:MM string to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes since midnight to HH:MM string."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (each as (start, end) in minutes) and the work period,
    return a list of free intervals within the work period.
    """
    free = []
    if not busy_intervals:
        return [(work_start, work_end)]
    busy_intervals.sort(key=lambda interval: interval[0])
    # Gap from work_start to the first busy interval
    if work_start < busy_intervals[0][0]:
        free.append((work_start, busy_intervals[0][0]))
    # Gaps between busy intervals
    for i in range(len(busy_intervals) - 1):
        current_end = busy_intervals[i][1]
        next_start = busy_intervals[i+1][0]
        if current_end < next_start:
            free.append((current_end, next_start))
    # Gap from last busy interval to work_end
    if busy_intervals[-1][1] < work_end:
        free.append((busy_intervals[-1][1], work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Returns the intersection between two lists of intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    intersection = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap between the two intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move to the next interval in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def main():
    meeting_duration = 30  # meeting duration in minutes

    # Define work hours for Monday
    work_start_str = "09:00"
    work_end_str = "17:00"
    work_start = parse_time(work_start_str)
    work_end = parse_time(work_end_str)
    
    # Define the schedules for each participant (busy intervals in HH:MM)
    schedules = {
        "John": [("11:30", "12:00"), ("14:00", "14:30")],
        "Megan": [("12:00", "12:30"), ("14:00", "15:00"), ("15:30", "16:00")],
        "Brandon": [],
        "Kimberly": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Sean": [("10:00", "11:00"), ("11:30", "14:00"), ("15:00", "15:30")],
        "Lori": [("09:00", "09:30"), ("10:30", "12:00"), ("13:00", "14:30"), ("16:00", "16:30")]
    }
    
    # Compute free intervals for each participant within work hours
    free_times = {}
    for person, intervals in schedules.items():
        busy_intervals = [(parse_time(start), parse_time(end)) for start, end in intervals]
        free_times[person] = get_free_intervals(busy_intervals, work_start, work_end)
    
    # Compute the common free intervals across all participants
    participants = list(schedules.keys())
    common_free = free_times[participants[0]]
    for person in participants[1:]:
        common_free = intersect_intervals(common_free, free_times[person])
    
    # Find the earliest free interval that can accommodate the meeting duration
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break
    
    if meeting_slot:
        start_time_str = minutes_to_time(meeting_slot[0])
        end_time_str = minutes_to_time(meeting_slot[1])
        day = "Monday"
        # Output the meeting day and time in the specified format: HH:MM:HH:MM
        print(f"{day} {{{start_time_str}:{end_time_str}}}")
    else:
        print("No common time slot available.")

if __name__ == "__main__":
    main()