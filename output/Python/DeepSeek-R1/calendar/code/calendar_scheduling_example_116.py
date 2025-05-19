def schedule_meeting():
    # Define work hours and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30

    # Convert schedules to minutes since midnight
    schedules = {
        'Adam': [(14*60, 15*60)],
        'John': [(13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)],
        'Stephanie': [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 16*60), (16*60+30, 17*60)],
        'Anna': [(9*60+30, 10*60), (12*60, 12*60+30), (13*60, 15*60+30), (16*60+30, 17*60)],
    }

    # Generate free slots for each person
    free_slots = {}
    for person, busy in schedules.items():
        slots = []
        prev_end = work_start
        for start, end in sorted(busy):
            if start > prev_end:
                slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            slots.append((prev_end, work_end))
        free_slots[person] = slots

    # Apply Anna's preference (not before 14:30)
    anna_pref_start = 14*60 + 30
    free_slots['Anna'] = [slot for slot in free_slots['Anna'] if slot[0] >= anna_pref_start]

    # Find overlapping slots
    common_slots = []
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        end_time = current_time + meeting_duration
        all_available = True
        for person in free_slots:
            available = False
            for slot in free_slots[person]:
                if slot[0] <= current_time and end_time <= slot[1]:
                    available = True
                    break
            if not available:
                all_available = False
                break
        if all_available:
            common_slots.append((current_time, end_time))
        current_time += 15  # Check every 15 minutes

    # Select the earliest possible time
    if common_slots:
        best_start, best_end = common_slots[0]
        return "Monday", f"{best_start//60:02}:{best_start%60:02}:{best_end//60:02}:{best_end%60:02}"
    return "No time found", ""

# Execute and print result
day, time = schedule_meeting()
print(f"{day} {time}")