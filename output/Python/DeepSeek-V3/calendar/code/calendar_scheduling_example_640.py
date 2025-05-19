def find_meeting_time(bobby_busy, michael_busy, work_hours, duration, days):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m - 540  # Subtract 540 to start from 0 (9:00)

    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    # Generate free slots for a person
    def get_free_slots(busy_slots, day_hours):
        free_slots = []
        start_of_day = time_to_minutes(day_hours[0])
        end_of_day = time_to_minutes(day_hours[1])
        
        # Sort busy slots by start time
        busy_slots_sorted = sorted(busy_slots, key=lambda x: x[0])
        
        # Check before first busy slot
        if busy_slots_sorted and busy_slots_sorted[0][0] > start_of_day:
            free_slots.append((start_of_day, busy_slots_sorted[0][0]))
        
        # Check between busy slots
        for i in range(len(busy_slots_sorted) - 1):
            current_end = busy_slots_sorted[i][1]
            next_start = busy_slots_sorted[i+1][0]
            if next_start > current_end:
                free_slots.append((current_end, next_start))
        
        # Check after last busy slot
        if busy_slots_sorted and busy_slots_sorted[-1][1] < end_of_day:
            free_slots.append((busy_slots_sorted[-1][1], end_of_day))
        
        # If no busy slots, the whole day is free
        if not busy_slots_sorted:
            free_slots.append((start_of_day, end_of_day))
        
        return free_slots

    # Find overlapping free slots between two people
    def find_overlapping_slots(slots1, slots2, duration):
        overlapping = []
        for s1 in slots1:
            for s2 in slots2:
                start = max(s1[0], s2[0])
                end = min(s1[1], s2[1])
                if end - start >= duration:
                    overlapping.append((start, end))
        return overlapping

    # Process each day
    for day in days:
        # Get Bobby's busy slots for the day in minutes
        bobby_day_busy = []
        for slot in bobby_busy.get(day, []):
            start, end = map(time_to_minutes, slot.split(' to '))
            bobby_day_busy.append((start, end))
        
        # Get Michael's busy slots for the day in minutes
        michael_day_busy = []
        for slot in michael_busy.get(day, []):
            start, end = map(time_to_minutes, slot.split(' to '))
            michael_day_busy.append((start, end))
        
        # Get free slots for both
        bobby_free = get_free_slots(bobby_day_busy, work_hours)
        michael_free = get_free_slots(michael_day_busy, work_hours)
        
        # Find overlapping slots
        overlapping = find_overlapping_slots(bobby_free, michael_free, duration)
        
        if overlapping:
            # Choose the earliest slot
            earliest_start = overlapping[0][0]
            meeting_start = minutes_to_time(earliest_start)
            meeting_end = minutes_to_time(earliest_start + duration)
            return f"{day}:{meeting_start}:{meeting_end}"
    
    return "No suitable time found."

# Define inputs
bobby_busy = {
    "Monday": ["14:30 to 15:00"],
    "Tuesday": ["9:00 to 11:30", "12:00 to 12:30", "13:00 to 15:00", "15:30 to 17:00"]
}

michael_busy = {
    "Monday": ["9:00 to 10:00", "10:30 to 13:30", "14:00 to 15:00", "15:30 to 17:00"],
    "Tuesday": ["9:00 to 10:30", "11:00 to 11:30", "12:00 to 14:00", "15:00 to 16:00", "16:30 to 17:00"]
}

work_hours = ["9:00", "17:00"]
duration = 30  # minutes
days = ["Monday", "Tuesday"]

# Find and print the meeting time
result = find_meeting_time(bobby_busy, michael_busy, work_hours, duration, days)
print(result)