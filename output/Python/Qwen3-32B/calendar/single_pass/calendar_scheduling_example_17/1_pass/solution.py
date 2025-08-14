work_start = 9 * 60
work_end_meeting_start = 13 * 60
meeting_duration = 30

# Participants' blocked times
blocked_margaret = [
    (9*60, 10*60),
    (10*60 + 30, 11*60),
    (11*60 + 30, 12*60),
    (13*60, 13*60 + 30),
    (15*60, 15*60 + 30)
]
blocked_donna = [
    (14*60 + 30, 15*60),
    (16*60, 16*60 + 30)
]
blocked_helen = [
    (9*60, 9*60 + 30),
    (10*60, 11*60 + 30),
    (13*60, 14*60),
    (14*60 + 30, 15*60),
    (15*60 + 30, 17*60)
]

def process_blocked_times(blocked_times, work_start, work_end):
    processed = []
    for start, end in blocked_times:
        start_in_window = max(start, work_start)
        end_in_window = min(end, work_end)
        if start_in_window < end_in_window:
            processed.append( (start_in_window, end_in_window) )
    processed.sort()
    return processed

def merge_intervals(intervals):
    if not intervals:
        return []
    merged = [list(intervals[0])]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            last[1] = max(last[1], current[1])
        else:
            merged.append(list(current))
    return [tuple(interval) for interval in merged]

def get_available_slots(work_start, work_end, merged_blocked):
    available = []
    prev_end = work_start
    for start, end in merged_blocked:
        if prev_end < start:
            available.append( (prev_end, start) )
        prev_end = end
    if prev_end < work_end:
        available.append( (prev_end, work_end) )
    return available

def get_start_time_intervals(available_slots, meeting_duration):
    start_intervals = []
    for s, e in available_slots:
        if e - s >= meeting_duration:
            start_intervals.append( (s, e - meeting_duration) )
    return start_intervals

def compute_overlap(interval1, interval2):
    s_max = max(interval1[0], interval2[0])
    e_min = min(interval1[1], interval2[1])
    if s_max <= e_min:
        return (s_max, e_min)
    else:
        return None

def intersect_intervals(list1, list2):
    result = []
    for i1 in list1:
        for i2 in list2:
            overlap = compute_overlap(i1, i2)
            if overlap:
                result.append(overlap)
    return result

# Process each participant
# Margaret
blocked_margaret_processed = process_blocked_times(blocked_margaret, work_start, work_end_meeting_start)
merged_blocked_margaret = merge_intervals(blocked_margaret_processed)
available_slots_margaret = get_available_slots(work_start, work_end_meeting_start, merged_blocked_margaret)
start_intervals_margaret = get_start_time_intervals(available_slots_margaret, meeting_duration)

# Donna
blocked_donna_processed = process_blocked_times(blocked_donna, work_start, work_end_meeting_start)
merged_blocked_donna = merge_intervals(blocked_donna_processed)
available_slots_donna = get_available_slots(work_start, work_end_meeting_start, merged_blocked_donna)
start_intervals_donna = get_start_time_intervals(available_slots_donna, meeting_duration)

# Helen
blocked_helen_processed = process_blocked_times(blocked_helen, work_start, work_end_meeting_start)
merged_blocked_helen = merge_intervals(blocked_helen_processed)
available_slots_helen = get_available_slots(work_start, work_end_meeting_start, merged_blocked_helen)
start_intervals_helen = get_start_time_intervals(available_slots_helen, meeting_duration)

# Find intersection
start_intervals = start_intervals_margaret
start_intervals = intersect_intervals(start_intervals, start_intervals_donna)
start_intervals = intersect_intervals(start_intervals, start_intervals_helen)

# Find earliest start time
if start_intervals:
    earliest_start = min( [s for s, e in start_intervals] )
    earliest_end = earliest_start + meeting_duration
    # Convert to time strings
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    start_time = minutes_to_time(earliest_start)
    end_time = minutes_to_time(earliest_end)
    day = "Monday"
    print(f"{start_time}:{end_time} {day}")
else:
    print("No suitable time found.")