def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(working_start, working_end, busy_intervals):
    if not busy_intervals:
        return [(working_start, working_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    for interval in sorted_busy:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            curr_start, curr_end = interval
            if curr_start <= last_end:
                merged[-1] = (last_start, max(last_end, curr_end))
            else:
                merged.append(interval)
    free = []
    prev_end = working_start
    for start, end in merged:
        if prev_end < start:
            free.append( (prev_end, start) )
        prev_end = max(prev_end, end)
    if prev_end < working_end:
        free.append( (prev_end, working_end) )
    return free

def interval_intersection(intervals1, intervals2):
    i = 0
    j = 0
    res = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append( (start, end) )
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

def get_priority(day, start_time):
    if day == 'Tuesday':
        return 0
    elif day == 'Wednesday' and start_time >= 720:  # 12:00
        return 1
    elif day == 'Monday':
        return 2
    elif day == 'Wednesday' and start_time < 720:
        return 3
    else:
        return 4  # shouldn't happen

# Define working hours
working_start = 540  # 9:00 AM
working_end = 1020   # 5:00 PM

# Busy intervals for each participant per day
judith_busy = {
    'Monday': [(720, 750)],  # 12:00-12:30
    'Wednesday': [(690, 720)],  # 11:30-12:00
}

timothy_busy = {
    'Monday': [(570, 600), (630, 690), (750, 840), (930, 1020)],  # 9:30-10:00, etc.
    'Tuesday': [(570, 780), (780, 840), (870, 1020)],  # 9:30-13:00, etc.
    'Wednesday': [(540, 570), (630, 660), (810, 870), (900, 930), (960, 990)],  # 9:00-9:30, etc.
}

days = ['Monday', 'Tuesday', 'Wednesday']
possible_meetings = []

for day in days:
    # Get busy intervals for each participant on this day
    judith_day_busy = judith_busy.get(day, [])
    timothy_day_busy = timothy_busy.get(day, [])
    
    # Compute free intervals for each participant
    judith_free = get_free_intervals(working_start, working_end, judith_day_busy)
    timothy_free = get_free_intervals(working_start, working_end, timothy_day_busy)
    
    # Find intersection of free intervals
    common_free = interval_intersection(judith_free, timothy_free)
    
    # Check for intervals that can fit a one-hour meeting (60 minutes)
    for start, end in common_free:
        if end - start >= 60:
            # Add the earliest possible one-hour meeting in this interval
            possible_meetings.append( (day, start, start + 60) )

# Sort possible meetings by priority
possible_meetings.sort(key=lambda x: get_priority(x[0], x[1]))

# Select the first one (highest priority)
best_meeting = possible_meetings[0]
day, start, end = best_meeting

start_time = minutes_to_time(start)
end_time = minutes_to_time(end)

print(f"{start_time}:{end_time} {day}")