def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    # Sort intervals by start time.
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last_start, last_end = merged[-1]
        current_start, current_end = current
        # If intervals overlap or touch, merge them.
        if current_start <= last_end:
            merged[-1] = (last_start, max(last_end, current_end))
        else:
            merged.append(current)
    return merged

# Meeting settings
meeting_duration = 60  # in minutes
work_start = 9 * 60    # 9:00 in minutes (540)
work_end = 17 * 60     # 17:00 in minutes (1020)
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Participants' busy schedules (times are in minutes since midnight)
busy = {
    "Nicole": {
        "Monday": [],
        "Tuesday": [(16 * 60, 16 * 60 + 30)],              # 16:00-16:30
        "Wednesday": [(15 * 60, 15 * 60 + 30)],              # 15:00-15:30
        "Thursday": [],
        "Friday": [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]  # 12:00-12:30 and 15:30-16:00
    },
    "Daniel": {
        "Monday": [(9 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 16 * 60 + 30)],
        "Tuesday": [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30),
                    (13 * 60, 13 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
        "Wednesday": [(9 * 60, 10 * 60), (11 * 60, 12 * 60 + 30),
                      (13 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
        "Thursday": [(11 * 60, 12 * 60), (13 * 60, 14 * 60), (15 * 60, 15 * 60 + 30)],
        "Friday": [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60),
                   (12 * 60 + 30, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }
}

# Iterate days in order to find the earliest available slot.
meeting_found = False
for day in days:
    intervals = []
    # Add Nicole's busy intervals for the day.
    intervals.extend(busy["Nicole"].get(day, []))
    # Add Daniel's busy intervals for the day.
    intervals.extend(busy["Daniel"].get(day, []))
    
    # Merge overlapping intervals.
    busy_merged = merge_intervals(intervals)
    
    # Compute free intervals within work hours.
    free_intervals = []
    if not busy_merged:
        free_intervals.append((work_start, work_end))
    else:
        # Check free period before the first busy interval.
        if work_start < busy_merged[0][0]:
            free_intervals.append((work_start, busy_merged[0][0]))
        # Check gaps between busy intervals.
        for i in range(len(busy_merged) - 1):
            gap_start = busy_merged[i][1]
            gap_end = busy_merged[i+1][0]
            if gap_end - gap_start > 0:
                free_intervals.append((gap_start, gap_end))
        # Check free period after the last busy interval.
        if busy_merged[-1][1] < work_end:
            free_intervals.append((busy_merged[-1][1], work_end))
    
    # Look for the earliest free interval that can accommodate the meeting.
    for free_start, free_end in free_intervals:
        if free_end - free_start >= meeting_duration:
            meeting_start = free_start
            meeting_end = free_start + meeting_duration
            print(f"{day}: {{{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}}}")
            meeting_found = True
            break
    if meeting_found:
        break

if not meeting_found:
    print("No available slot found.")