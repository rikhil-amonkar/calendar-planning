def find_meeting_time():
    # Participants' busy intervals in minutes since midnight
    denise = [(12*60, 12*60+30), (15*60+30, 16*60)]
    angela = []
    natalie = [(9*60, 11*60+30), (12*60, 13*60), (14*60, 14*60+30), (15*60, 17*60)]
    
    # Combine all busy intervals
    busy_intervals = denise + angela + natalie
    # Sort intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping intervals
    merged = []
    for interval in busy_intervals:
        if not merged or merged[-1][1] < interval[0]:
            merged.append(interval)
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], interval[1]))
    
    # Work hours 9:00 (540) to 17:00 (1020)
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # minutes
    
    current_start = work_start
    # Check gaps between merged intervals
    for start, end in merged:
        if start > current_start:
            if start - current_start >= duration:
                # Found a suitable slot
                return format_time(current_start, current_start + duration, "Monday")
        current_start = max(current_start, end)
    # Check after last interval
    if work_end - current_start >= duration:
        return format_time(current_start, current_start + duration, "Monday")
    return None

def format_time(start, end, day):
    def to_hhmm(minutes):
        return f"{minutes//60:02}:{minutes%60:02}"
    return f"{day} {to_hhmm(start)}:{to_hhmm(end)}"

# Find and print the meeting time
result = find_meeting_time()
print(result)