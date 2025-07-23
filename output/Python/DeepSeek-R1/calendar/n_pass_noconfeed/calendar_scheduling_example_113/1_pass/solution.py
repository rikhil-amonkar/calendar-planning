def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define busy times for each person (start_minute, end_minute)
    bradley_busy = [(570, 600), (750, 780), (810, 840), (930, 960)]
    teresa_busy = [(630, 660), (720, 750), (780, 810), (870, 900)]
    elizabeth_busy = [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)]
    christian_busy = [(540, 570), (630, 1020)]
    
    # Function to compute free slots given busy slots and work hours
    def get_free_slots(busy_slots, work_start, work_end):
        if not busy_slots:
            return [(work_start, work_end)]
        busy_sorted = sorted(busy_slots, key=lambda x: x[0])
        free_slots = []
        current = work_start
        for start, end in busy_sorted:
            if current < start:
                free_slots.append((current, start))
            current = max(current, end)
        if current < work_end:
            free_slots.append((current, work_end))
        return free_slots

    # Get free slots for each person
    free_bradley = get_free_slots(bradley_busy, work_start, work_end)
    free_teresa = get_free_slots(teresa_busy, work_start, work_end)
    free_elizabeth = get_free_slots(elizabeth_busy, work_start, work_end)
    free_christian = get_free_slots(christian_busy, work_start, work_end)
    
    # Function to intersect two lists of intervals
    def intersect_intervals(intervals1, intervals2):
        i, j = 0, 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            low = max(intervals1[i][0], intervals2[j][0])
            high = min(intervals1[i][1], intervals2[j][1])
            if low < high:
                result.append((low, high))
            if intervals1[i][1] < intervals2[j][1]:
                i += 1
            else:
                j += 1
        return result

    # Compute common free intervals for all
    common_free = free_bradley
    for free_slots in [free_teresa, free_elizabeth, free_christian]:
        common_free = intersect_intervals(common_free, free_slots)
    
    # Find the first common free slot of sufficient duration
    meeting_start = None
    meeting_end = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    # Convert minutes to HH:MM format
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    
    # Output day and time in HH:MM:HH:MM format
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()