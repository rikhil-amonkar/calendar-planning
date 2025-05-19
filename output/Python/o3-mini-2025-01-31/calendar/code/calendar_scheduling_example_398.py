def to_minutes(time_str):
    """Convert HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_time_str(minutes):
    """Convert minutes since midnight to HH:MM format."""
    return f"{minutes//60:02}:{minutes%60:02}"

def subtract_busy(free, busy):
    """Subtract busy interval from a free interval (both as [start, end])."""
    free_start, free_end = free
    busy_start, busy_end = busy
    result = []
    # if busy interval does not overlap with free interval, return free
    if busy_end <= free_start or busy_start >= free_end:
        return [free]
    # if there is a free portion before the busy interval:
    if busy_start > free_start:
        result.append([free_start, busy_start])
    # if there is free portion after the busy interval:
    if busy_end < free_end:
        result.append([busy_end, free_end])
    return result

def merge_intervals(intervals):
    """Merge overlapping intervals if needed (assumed sorted by start)."""
    if not intervals:
        return []
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = [last[0], max(last[1], current[1])]
        else:
            merged.append(current)
    return merged

def compute_free_intervals(busy_intervals, work_start, work_end):
    """Compute free intervals given busy intervals within work hours."""
    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = [[work_start, work_end]]
    for busy in busy_intervals:
        new_free = []
        for free in free_intervals:
            new_free.extend(subtract_busy(free, busy))
        free_intervals = new_free
    return free_intervals

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals."""
    i, j = 0, 0
    res = []
    while i < len(list1) and j < len(list2):
        # Find overlap between intervals
        start = max(list1[i][0], list2[j][0])
        end = min(list1[i][1], list2[j][1])
        if start < end:
            res.append([start, end])
        # Move to next interval
        if list1[i][1] < list2[j][1]:
            i += 1
        else:
            j += 1
    return res

def find_common_free_interval(free_lists, duration):
    """Find the earliest common free interval of at least 'duration' minutes from a list of free intervals lists."""
    # Intersect all free intervals
    common = free_lists[0]
    for free in free_lists[1:]:
        common = intersect_intervals(common, free)
        if not common:
            return None
    # Look for an interval that fits the duration
    for interval in common:
        if interval[1] - interval[0] >= duration:
            return interval[0], interval[0] + duration
    return None

def main():
    # Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    meeting_duration = 30

    # Busy schedules for each participant on Monday (times in HH:MM strings, converted to minutes)
    schedules = {
        "Doris": [("09:00", "11:00"), ("13:30", "14:00"), ("16:00", "16:30")],
        "Theresa": [("10:00", "12:00")],
        "Christian": [],  # No meetings
        "Terry": [("09:30", "10:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                  ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
        "Carolyn": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"),
                    ("13:30", "14:30"), ("15:00", "17:00")],
        "Kyle": [("09:00", "09:30"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:30", "17:00")]
    }

    # Compute free intervals for each participant
    free_intervals_list = []
    for person, busy_times in schedules.items():
        busy_minutes = []
        for start, end in busy_times:
            busy_minutes.append([to_minutes(start), to_minutes(end)])
        free_intervals = compute_free_intervals(busy_minutes, work_start, work_end)
        # Ensure intervals are merged (though they should not overlap in each individual's schedule)
        free_intervals = merge_intervals(free_intervals)
        free_intervals_list.append(free_intervals)

    meeting_time = find_common_free_interval(free_intervals_list, meeting_duration)
    if meeting_time:
        start_time_str = to_time_str(meeting_time[0])
        end_time_str = to_time_str(meeting_time[1])
        day = "Monday"
        print(f"{day} {start_time_str}:{end_time_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()