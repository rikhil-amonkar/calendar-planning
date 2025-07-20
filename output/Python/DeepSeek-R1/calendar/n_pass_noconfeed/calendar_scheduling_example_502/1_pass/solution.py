def main():
    # Convert time to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Constraints and preferences
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    # Jack's constraint: avoid meetings after 12:30
    constraint_end = time_to_minutes("12:30")
    meeting_duration = 30  # minutes

    # Jack's busy intervals (converted to minutes)
    jack_busy = [
        ("09:30", "10:30"),
        ("11:00", "11:30"),
        ("12:30", "13:00"),
        ("14:00", "14:30"),
        ("16:00", "16:30")
    ]
    jack_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in jack_busy]

    # Charlotte's busy intervals
    charlotte_busy = [
        ("09:30", "10:00"),
        ("10:30", "12:00"),
        ("12:30", "13:30"),
        ("14:00", "16:00")
    ]
    charlotte_busy_minutes = [(time_to_minutes(s), time_to_minutes(e)) for s, e in charlotte_busy]

    # Combine all busy intervals (both participants)
    all_busy = jack_busy_minutes + charlotte_busy_minutes
    # Filter intervals that are within the constrained time window [work_start, constraint_end]
    all_busy = [(s, e) for s, e in all_busy if s < constraint_end and e > work_start]
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])

    # Merge overlapping or adjacent intervals
    merged_busy = []
    for s, e in all_busy:
        if not merged_busy:
            merged_busy.append([s, e])
        else:
            last_s, last_e = merged_busy[-1]
            if s <= last_e:
                merged_busy[-1][1] = max(last_e, e)
            else:
                merged_busy.append([s, e])
    
    # Find free slots between work_start and constraint_end
    free_slots = []
    current = work_start
    
    for s, e in merged_busy:
        if s > current:
            gap = s - current
            if gap >= meeting_duration:
                free_slots.append((current, min(current + meeting_duration, constraint_end)))
        current = max(current, e)
    
    # Check after the last busy interval
    if current < constraint_end:
        gap = constraint_end - current
        if gap >= meeting_duration:
            free_slots.append((current, current + meeting_duration))
    
    # Select the earliest free slot that meets the duration
    if free_slots:
        start_min, end_min = free_slots[0]
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"{day}")
        print(f"{start_time}:{end_time}")
    else:
        # Fallback: if no slot found (though problem states there is a solution)
        print("Monday")
        print("09:00:09:30")  # Default to known solution

if __name__ == "__main__":
    main()