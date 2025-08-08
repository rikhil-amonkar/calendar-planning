def time_to_minutes(time_str):
    """Convert HH:MM time format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM time format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Given busy intervals (in minutes) and work start/end, return free intervals."""
    free = []
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    # Free time before the first busy interval
    if work_start < busy_intervals[0][0]:
        free.append((work_start, busy_intervals[0][0]))
    # Free time between busy intervals
    for i in range(len(busy_intervals) - 1):
        if busy_intervals[i][1] < busy_intervals[i+1][0]:
            free.append((busy_intervals[i][1], busy_intervals[i+1][0]))
    # Free time after the last busy interval
    if busy_intervals[-1][1] < work_end:
        free.append((busy_intervals[-1][1], work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Find intersections between two lists of intervals."""
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list which has the earlier finishing time
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def main():
    # Meeting details
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    day = "Monday"
    
    # Busy intervals for Lisa on Monday (in minutes)
    lisa_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("16:00"))
    ]
    
    # Busy intervals for Anthony on Monday (in minutes)
    anthony_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Calculate free intervals within work hours for each participant
    lisa_free = get_free_intervals(lisa_busy, work_start, work_end)
    anthony_free = get_free_intervals(anthony_busy, work_start, work_end)
    
    # Find common free intervals
    common_free = intersect_intervals(lisa_free, anthony_free)
    
    # Find the earliest available slot that fits the meeting duration
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break
    
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        print(f"{day} {start_time}:{end_time}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()