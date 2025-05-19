def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Define the meeting duration
    meeting_duration = 30  # 30 minutes

    # Jack's busy periods on Monday
    jack_busy = [
        (9 * 60 + 30, 10 * 60),   # 9:30-10:00
        (11 * 60, 11 * 60 + 30), # 11:00-11:30
        (12 * 60 + 30, 13 * 60), # 12:30-13:00
        (14 * 60, 14 * 60 + 30), # 14:00-14:30
        (16 * 60, 16 * 60 + 30)  # 16:00-16:30
    ]

    # Charlotte's busy periods on Monday
    charlotte_busy = [
        (9 * 60, 10 * 60),       # 9:30-10:00
        (10 * 60, 12 * 60),      # 10:30-12:00
        (12 * 60, 13 * 60),      # 12:30-13:00
        (14 * 60, 16 * 60)       # 14:00-16:00
    ]

    # Find all free slots for Jack and Charlotte
    def get_free_slots(busy_times):
        free = []
        for slot in range(work_start, work_end + 1, 60):
            slot_start = slot
            slot_end = slot + 30
            if slot_end > work_end:
                slot_end = work_end
            for b in busy_times:
                if b[0] <= slot_start < b[1] or b[0] <= slot_end - 1 < b[1]:
                    break
            else:
                free.append((slot_start, slot_end))
        return free

    jack_free = get_free_slots(jack_busy)
    charlotte_free = get_free_slots(charlotte_busy)

    # Find common free slots
    common_free = []
    for j in jack_free:
        for c in charlotte_free:
            if j[0] < c[0] and j[1] > c[1]:
                continue
            if j[0] >= c[0] and j[1] <= c[1]:
                continue
            common_free.append(j)

    if not common_free:
        return None

    # Jack prefers no meetings after 12:30
    latest_possible = None
    for slot in common_free:
        if slot[0] < 12 * 60 and slot[1] > slot[0] + meeting_duration:
            if latest_possible is None or slot[1] > latest_possible[1]:
                latest_possible = slot

    if latest_possible:
        return f"{latest_possible[0]:02d}:{latest_possible[1]:02d}:Monday"
    else:
        return None

# Run the function and print the result
result = find_meeting_time()
if result:
    print(result)
else:
    print("No suitable time found")