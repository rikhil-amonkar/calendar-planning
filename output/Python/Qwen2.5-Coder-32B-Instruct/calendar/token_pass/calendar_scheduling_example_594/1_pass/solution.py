def find_meeting_time(participants, meeting_duration, work_start, work_end):
    from collections import defaultdict

    # Step 1: Parse the input data
    busy_times = defaultdict(list)
    for name, times in participants.items():
        busy_times[name] = sorted(times)

    # Step 2: Determine available time slots for each participant
    available_slots = defaultdict(list)
    for name, times in busy_times.items():
        last_end = work_start
        for start, end in times:
            if start > last_end:
                available_slots[name].append((last_end, start))
            last_end = max(last_end, end)
        if last_end < work_end:
            available_slots[name].append((last_end, work_end))

    # Step 3: Find common free time slots
    common_slots = []
    for start1, end1 in available_slots[next(iter(available_slots))]:
        valid_for_all = True
        for name, slots in available_slots.items():
            found_overlap = False
            for start2, end2 in slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= meeting_duration:
                    found_overlap = True
                    break
            if not found_overlap:
                valid_for_all = False
                break
        if valid_for_all:
            common_slots.append((start1, start1 + meeting_duration))

    # Step 4: Select the earliest suitable slot
    if common_slots:
        earliest_slot = min(common_slots, key=lambda x: x[0])
        return f"{earliest_slot[0]:02}:{earliest_slot[1]-earliest_slot[0]:02}:00:00", "Monday"
    else:
        return "No common slot found", "Monday"

# Example usage
participants = {
    'Adam': [(9, 10), (12.5, 13), (14.5, 15), (16.5, 17)],
    'Roy': [(10, 11), (11.5, 13), (13.5, 14.5), (16.5, 17)]
}
meeting_duration = 0.5  # in hours
work_start = 9  # in hours
work_end = 17  # in hours

time, day = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"Meeting time: {time} on {day}")