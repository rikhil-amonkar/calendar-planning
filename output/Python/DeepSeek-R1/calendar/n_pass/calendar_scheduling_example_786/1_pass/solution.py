def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours and meeting duration
work_start = time_to_minutes("9:00")  # 540 minutes
work_end = time_to_minutes("17:00")   # 1020 minutes
slot_duration = 30  # minutes

# Days to consider
days = ['Monday', 'Tuesday', 'Wednesday']

# Busy intervals for each day (converted to minutes)
busy_intervals_by_day = {
    'Monday': [
        (time_to_minutes("9:00"), time_to_minutes("10:30")),  # Pamela
        (time_to_minutes("11:00"), time_to_minutes("16:30"))  # Pamela
    ],
    'Tuesday': [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),   # Pamela
        (time_to_minutes("10:00"), time_to_minutes("17:00"))  # Pamela
    ],
    'Wednesday': [
        # Pamela
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30")),
        # Amy
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00"))
    ]
}

# Find all free slots
free_slots = []
for day in days:
    intervals = busy_intervals_by_day[day]
    # Check each 30-minute slot in the work day
    start = work_start
    while start <= work_end - slot_duration:
        end = start + slot_duration
        slot_free = True
        # Check against each busy interval
        for (b_start, b_end) in intervals:
            if start < b_end and b_start < end:
                slot_free = False
                break
        if slot_free:
            free_slots.append((day, start, end))
        start += slot_duration

# Assign priorities based on preferences
candidate_slots = []
for (day, start, end) in free_slots:
    if day == 'Wednesday' and start >= time_to_minutes("16:00"):
        priority = 0
    elif day == 'Tuesday' and start >= time_to_minutes("16:00"):
        priority = 1
    elif day == 'Wednesday' and start < time_to_minutes("16:00"):
        priority = 2
    elif day == 'Tuesday' and start < time_to_minutes("16:00"):
        priority = 3
    else:  # Monday
        priority = 4
    candidate_slots.append((priority, day, start, end))

# Sort by priority (lowest first) and pick the best candidate
candidate_slots.sort(key=lambda x: x[0])
best_priority, best_day, best_start, best_end = candidate_slots[0]

# Format the time string as HH:MM:HH:MM
start_time_str = minutes_to_time(best_start)
end_time_str = minutes_to_time(best_end)
time_range_str = f"{start_time_str}:{end_time_str}"

# Output the day and time range
print(best_day)
print(time_range_str)