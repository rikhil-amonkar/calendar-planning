from datetime import datetime, timedelta

# Participants' schedules
schedules = {
    'Evelyn': [(timedelta(hours=9), timedelta(hours=17))],
    'Joshua': [(timedelta(hours=9), timedelta(hours=11)),
               (timedelta(hours=12, minutes=30), timedelta(hours=13, minutes=30)),
               (timedelta(hours=14, minutes=30), timedelta(hours=16, minutes=30)),
               (timedelta(hours=17), timedelta(hours=17))],
    'Kevin': [(timedelta(hours=9), timedelta(hours=17))],
    'Gerald': [(timedelta(hours=9), timedelta(hours=17))],
    'Jerry': [(timedelta(hours=9, minutes=30), timedelta(hours=10, minutes=30)),
              (timedelta(hours=12), timedelta(hours=12, minutes=30)),
              (timedelta(hours=13), timedelta(hours=13, minutes=30)),
              (timedelta(hours=14), timedelta(hours=14, minutes=30)),
              (timedelta(hours=15), timedelta(hours=15, minutes=30)),
              (timedelta(hours=16), timedelta(hours=16, minutes=30)),
              (timedelta(hours=17), timedelta(hours=17))],
    'Jesse': [(timedelta(hours=9, minutes=30), timedelta(hours=10, minutes=30)),
              (timedelta(hours=12), timedelta(hours=12, minutes=30)),
              (timedelta(hours=13), timedelta(hours=14, minutes=30)),
              (timedelta(hours=15), timedelta(hours=15, minutes=30)),
              (timedelta(hours=16, minutes=30), timedelta(hours=17))],
    'Kenneth': [(timedelta(hours=10, minutes=30), timedelta(hours=12, minutes=30)),
                (timedelta(hours=13, minutes=30), timedelta(hours=14)),
                (timedelta(hours=14, minutes=30), timedelta(hours=15)),
                (timedelta(hours=15, minutes=30), timedelta(hours=16)),
                (timedelta(hours=16, minutes=30), timedelta(hours=17))]
}

def find_meeting_time(duration_hours, duration_minutes):
    duration = timedelta(hours=duration_hours, minutes=duration_minutes)
    day = "Monday"
    
    # Create a list of all free time slots for all participants
    all_free_slots = []
    for participant, busy_times in schedules.items():
        free_slots = []
        start_of_day = timedelta(hours=9)
        end_of_day = timedelta(hours=17)

        # Calculate free slots
        if busy_times:
            busy_times = sorted(busy_times, key=lambda x: x[0])  # Sort busy times
            busy_times = [(start_of_day, busy_times[0][0])] + busy_times + [(busy_times[-1][1], end_of_day)]
            
            for i in range(len(busy_times) - 1):
                free_slot_start = busy_times[i][1]
                free_slot_end = busy_times[i + 1][0]
                if free_slot_end - free_slot_start >= duration:
                    free_slots.append((free_slot_start, free_slot_end))
        else:
            free_slots = [(start_of_day, end_of_day)]

        all_free_slots.append(free_slots)

    # Find common free slots
    common_free_slots = all_free_slots[0]
    for slots in all_free_slots[1:]:
        new_common_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in slots:
                start = max(start1, start2)
                end = min(end1, end2)
                if end - start >= duration:
                    new_common_slots.append((start, end))
        common_free_slots = new_common_slots

    # Select the first available time slot
    if common_free_slots:
        start_time = common_free_slots[0][0]
        end_time = start_time + duration
        return f"{start_time.seconds//3600:02}:{(start_time.seconds//60)%60:02}:{end_time.seconds//3600:02}:{(end_time.seconds//60)%60:02} ({day})"
    
    return "No available time slots found."

# Proposed meeting duration is 1 hour
print(find_meeting_time(1, 0))