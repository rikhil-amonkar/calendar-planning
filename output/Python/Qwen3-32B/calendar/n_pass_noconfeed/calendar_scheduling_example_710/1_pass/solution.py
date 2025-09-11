def is_slot_free(slot_start, slot_end, busy_intervals):
    for b_start, b_end in busy_intervals:
        if slot_start < b_end and b_start < slot_end:
            return False
    return True

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define busy intervals in minutes since midnight
busy_cheryl = {
    'Monday': [(9 * 60, 9 * 60 + 30), (11 * 60 + 30, 13 * 60), (15 * 60 + 30, 16 * 60)],
    'Tuesday': [(15 * 60, 15 * 60 + 30)],
    'Wednesday': []
}

busy_kyle = {
    'Monday': [(9 * 60, 17 * 60)],
    'Tuesday': [(9 * 60 + 30, 17 * 60)],
    'Wednesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 13 * 60), (13 * 60 + 30, 14 * 60)]
}

# Check each day
for day in ['Monday', 'Tuesday']:
    cheryl_intervals = busy_cheryl.get(day, [])
    kyle_intervals = busy_kyle.get(day, [])
    # Iterate through possible start times
    for start in range(9 * 60, 17 * 60 - 30 + 1):
        end = start + 30
        cheryl_free = is_slot_free(start, end, cheryl_intervals)
        kyle_free = is_slot_free(start, end, kyle_intervals)
        if cheryl_free and kyle_free:
            start_time = minutes_to_time(start)
            end_time = minutes_to_time(end)
            print(f"{{{start_time}:{end_time}}} {day}")
            exit()