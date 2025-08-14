def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    # Sort by start time
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            # Overlapping or adjacent, merge
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slots(merged_busy):
    free_slots = []
    start_work = 540  # 9:00 AM
    end_work = 1020   # 5:00 PM

    if not merged_busy:
        # Entire day is free
        if end_work - start_work >= 30:
            free_slots.append( (start_work, end_work) )
    else:
        # Check before the first busy interval
        first = merged_busy[0]
        if first[0] > start_work:
            free_start = start_work
            free_end = first[0]
            if free_end - free_start >= 30:
                free_slots.append( (free_start, free_end) )

        # Check between busy intervals
        for i in range(1, len(merged_busy)):
            prev_end = merged_busy[i-1][1]
            curr_start = merged_busy[i][0]
            if curr_start - prev_end >= 30:
                free_slots.append( (prev_end, curr_start) )

        # Check after the last busy interval
        last = merged_busy[-1]
        if last[1] < end_work:
            free_start = last[1]
            free_end = end_work
            if free_end - free_start >= 30:
                free_slots.append( (free_start, free_end) )
    return free_slots

# Define the busy times for each participant
ronald_busy = {
    'Monday': [
        ('10:30', '11:00'),
        ('12:00', '12:30'),
        ('15:30', '16:00')
    ],
    'Tuesday': [
        ('9:00', '9:30'),
        ('12:00', '12:30'),
        ('15:30', '16:30')
    ],
    'Wednesday': [
        ('9:30', '10:30'),
        ('11:00', '12:00'),
        ('12:30', '13:00'),
        ('13:30', '14:00'),
        ('16:30', '17:00')
    ]
}

amber_busy = {
    'Monday': [
        ('9:00', '9:30'),
        ('10:00', '10:30'),
        ('11:30', '12:00'),
        ('12:30', '14:00'),
        ('14:30', '15:00'),
        ('15:30', '17:00')
    ],
    'Tuesday': [
        ('9:00', '9:30'),
        ('10:00', '11:30'),
        ('12:00', '12:30'),
        ('13:30', '15:30'),
        ('16:30', '17:00')
    ],
    'Wednesday': [
        ('9:00', '9:30'),
        ('10:00', '10:30'),
        ('11:00', '13:30'),
        ('15:00', '15:30')
    ]
}

possible_slots = []

days = ['Monday', 'Tuesday', 'Wednesday']

for day in days:
    # Get Ronald's and Amber's busy times for this day
    ronald_day = ronald_busy.get(day, [])
    amber_day = amber_busy.get(day, [])
    
    # Convert to tuples of (start, end) in minutes
    ronald_intervals = [ (time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in ronald_day ]
    amber_intervals = [ (time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in amber_day ]
    
    # Combine
    combined = ronald_intervals + amber_intervals
    
    # Merge intervals
    merged = merge_intervals(combined)
    
    # Find free slots
    free_slots = find_free_slots(merged)
    
    # Add to possible_slots with day info
    for slot in free_slots:
        possible_slots.append( (day, slot[0], slot[1]) )

# Find the earliest possible slot
earliest_slot = min(possible_slots, key=lambda x: x[1])

day = earliest_slot[0]
start = earliest_slot[1]
end = earliest_slot[2]

start_str = minutes_to_time_str(start)
end_str = minutes_to_time_str(end)

print(f"{start_str}:{end_str} {day}")