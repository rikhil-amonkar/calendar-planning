def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def find_earliest_slot_for_day(busy_intervals):
    work_start = 540  # 9:00 AM
    work_end = 1020   # 5:00 PM
    sorted_buses = sorted(busy_intervals, key=lambda x: x[0])
    earliest_slot = None

    # Check before the first busy interval
    if sorted_buses:
        first_start = sorted_buses[0][0]
        free_start = work_start
        free_end = min(first_start, work_end)
        if free_end - free_start >= 60:
            slot_start = free_start
            slot_end = slot_start + 60
            if slot_end <= work_end:
                earliest_slot = (slot_start, slot_end)
    else:
        # No busy intervals, entire day is free
        earliest_slot = (work_start, work_start + 60)

    # Check between busy intervals
    for i in range(len(sorted_buses) - 1):
        prev_end = sorted_buses[i][1]
        next_start = sorted_buses[i+1][0]
        free_start = prev_end
        free_end = next_start
        if free_end - free_start >= 60:
            slot_start = free_start
            slot_end = slot_start + 60
            if slot_end <= work_end:
                if earliest_slot is None or slot_start < earliest_slot[0]:
                    earliest_slot = (slot_start, slot_end)

    # Check after the last busy interval
    if sorted_buses:
        last_end = sorted_buses[-1][1]
        free_start = last_end
        free_end = work_end
        if free_end - free_start >= 60:
            slot_start = free_start
            slot_end = slot_start + 60
            if slot_end <= work_end:
                if earliest_slot is None or slot_start < earliest_slot[0]:
                    earliest_slot = (slot_start, slot_end)

    return earliest_slot

# Roy's schedule in minutes
roy_schedule = {
    'Monday': [(600, 690), (720, 780), (840, 870), (900, 1020)],
    'Tuesday': [(630, 690), (720, 870), (900, 930), (960, 1020)],
    'Wednesday': [(570, 690), (750, 840), (870, 930), (990, 1020)],
}

days = ['Monday', 'Tuesday', 'Wednesday']
best_slot = None
best_day = None

for day in days:
    busy_intervals = roy_schedule[day]
    slot = find_earliest_slot_for_day(busy_intervals)
    if slot:
        if best_slot is None or slot[0] < best_slot[0]:
            best_slot = slot
            best_day = day

start_time = minutes_to_time(best_slot[0])
end_time = minutes_to_time(best_slot[1])

print(f"{start_time}:{end_time} {best_day}")