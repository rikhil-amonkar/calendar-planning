def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define the meeting duration
    meeting_duration = 30  # 30 minutes

    # Nancy's busy periods
    nancy_busy = [
        (10 * 60, 10 * 60 + 30),   # 10:00-10:30
        (11 * 60 + 30, 12 * 60),  # 11:30-12:30
        (13 * 60 + 30, 14 * 60),  # 13:30-14:00
        (14 * 60, 15 * 60 + 30),  # 14:30-15:30
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]
    nancy_busy_tuesday = [
        (9 * 60 + 30, 10 * 60),    # 9:30-10:00
        (11 * 60, 11 * 60 + 30),   # 11:00-11:30
        (12 * 60, 12 * 60 + 30),   # 12:00-12:30
        (13 * 60, 13 * 60 + 30),   # 13:00-13:30
        (15 * 60, 16 * 60)         # 15:30-16:00
    ]
    nancy_busy_wednesday = [
        (10 * 60, 11 * 60 + 30),   # 10:00-11:30
        (13 * 60 + 30, 16 * 60)    # 13:30-16:00
    ]

    # Jose's busy periods
    jose_busy = [
        (9 * 60, 17 * 60)          # 9:00-17:00 (Monday)
    ]
    jose_busy_tuesday = [
        (9 * 60, 17 * 60)          # 9:00-17:00 (Tuesday)
    ]
    jose_busy_wednesday = [
        (9 * 60, 9 * 60 + 30),      # 9:30-10:00
        (12 * 60, 13 * 60),        # 12:30-13:30
        (15 * 60, 17 * 60)         # 15:00-17:00
    ]

    # Function to check if time is free for a person
    def is_free(person_busy, start, end):
        for b in person_busy:
            if (b[0] <= start < b[1]) or (b[0] <= end - 1 < b[1]):
                return False
        return True

    # Check each day starting from Monday
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        if day == 'Monday':
            nancy_free = []
            for slot in range(work_start, work_end + 1, 60):
                slot_start = slot
                slot_end = slot + meeting_duration
                if slot_end > work_end:
                    slot_end = work_end
                if is_free(nancy_busy, slot_start, slot_end):
                    nancy_free.append((slot_start, slot_end))
            if not nancy_free:
                continue

            for n_slot in nancy_free:
                if is_free(jose_busy, n_slot[0], n_slot[1]):
                    return f"{n_slot[0]:02d}:{n_slot[1]:02d}:{day}"

        elif day == 'Tuesday':
            nancy_free = []
            for slot in range(work_start, work_end + 1, 60):
                slot_start = slot
                slot_end = slot + meeting_duration
                if slot_end > work_end:
                    slot_end = work_end
                if is_free(nancy_busy_tuesday, slot_start, slot_end):
                    nancy_free.append((slot_start, slot_end))
            if not nancy_free:
                continue

            for n_slot in nancy_free:
                if is_free(jose_busy_tuesday, n_slot[0], n_slot[1]):
                    return f"{n_slot[0]:02d}:{n_slot[1]:02d}:{day}"

        elif day == 'Wednesday':
            nancy_free = []
            for slot in range(work_start, work_end + 1, 60):
                slot_start = slot
                slot_end = slot + meeting_duration
                if slot_end > work_end:
                    slot_end = work_end
                if is_free(nancy_busy_wednesday, slot_start, slot_end):
                    nancy_free.append((slot_start, slot_end))
            if not nancy_free:
                continue

            for n_slot in nancy_free:
                if is_free(jose_busy_wednesday, n_slot[0], n_slot[1]):
                    return f"{n_slot[0]:02d}:{n_slot[1]:02d}:{day}"

    return None

# Run the function and print the result
result = find_meeting_time()
if result:
    print(result)
else:
    print("No suitable time found")