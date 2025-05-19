def find_meeting_time(participants_schedules, duration, work_hours_start, work_hours_end):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - work_hours_start * 60

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_hh = (minutes + work_hours_start * 60) // 60
        total_mm = (minutes + work_hours_start * 60) % 60
        return f"{total_hh:02d}:{total_mm:02d}"

    # Initialize the busy slots for all participants
    busy_slots = []
    for schedule in participants_schedules:
        person_busy = []
        for busy_range in schedule:
            start, end = busy_range
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            person_busy.append((start_min, end_min))
        busy_slots.append(person_busy)

    # Find all possible free slots for each person
    free_slots_per_person = []
    for person_busy in busy_slots:
        person_free = []
        # Start from work hours start (0 in minutes since we subtracted work_hours_start)
        prev_end = 0
        # Sort busy slots by start time
        sorted_busy = sorted(person_busy, key=lambda x: x[0])
        for busy_start, busy_end in sorted_busy:
            if busy_start > prev_end:
                person_free.append((prev_end, busy_start))
            prev_end = max(prev_end, busy_end)
        # Check the slot after last busy slot until work hours end
        work_end_min = (work_hours_end - work_hours_start) * 60
        if prev_end < work_end_min:
            person_free.append((prev_end, work_end_min))
        free_slots_per_person.append(person_free)

    # Find intersection of all free slots
    common_free_slots = free_slots_per_person[0]
    for person_free in free_slots_per_person[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free_slots) and j < len(person_free):
            slot1_start, slot1_end = common_free_slots[i]
            slot2_start, slot2_end = person_free[j]
            # Find the overlap
            overlap_start = max(slot1_start, slot2_start)
            overlap_end = min(slot1_end, slot2_end)
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            # Move the pointer which ends first
            if slot1_end < slot2_end:
                i += 1
            else:
                j += 1
        common_free_slots = new_common_free

    # Find the first slot that can fit the duration
    duration_min = duration * 60
    for slot_start, slot_end in common_free_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = minutes_to_time(slot_start)
            meeting_end = minutes_to_time(slot_start + duration_min)
            return meeting_start, meeting_end

    return None, None

# Define the participants' schedules
participants_schedules = [
    [("10:00", "10:30"), ("16:00", "16:30")],  # Stephanie
    [("10:00", "10:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:30", "17:00")],  # Cheryl
    [("09:30", "10:00"), ("10:30", "11:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],  # Bradley
    [("09:00", "12:00"), ("13:00", "13:30"), ("14:30", "17:00")],  # Steven
]

# Define meeting parameters
meeting_duration = 1  # in hours
work_hours_start = 9
work_hours_end = 17
day_of_week = "Monday"

# Find the meeting time
meeting_start, meeting_end = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

# Output the result
if meeting_start and meeting_end:
    print(f"{meeting_start}:{meeting_end}")
    print(day_of_week)
else:
    print("No suitable time found.")