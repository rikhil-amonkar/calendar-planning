def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def compute_free_intervals(busy_intervals, day_start, day_end):
    if not busy_intervals:
        return [(day_start, day_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = day_start
    for start, end in sorted_busy:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < day_end:
        free_intervals.append((current, day_end))
    return free_intervals

def intersect_two_interval_lists(list1, list2):
    if not list1 or not list2:
        return []
    common = []
    for iv1 in list1:
        for iv2 in list2:
            low = max(iv1[0], iv2[0])
            high = min(iv1[1], iv2[1])
            if low < high:
                common.append((low, high))
    return common

def main():
    day_start = time_str_to_minutes("9:00")
    day_end = time_str_to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Define busy intervals for each participant in minutes
    participants_busy = {
        "Wayne": [],
        "Melissa": [
            ("10:00", "11:00"),
            ("12:30", "14:00"),
            ("15:00", "15:30")
        ],
        "Catherine": [],
        "Gregory": [
            ("12:30", "13:00"),
            ("15:30", "16:00")
        ],
        "Victoria": [
            ("9:00", "9:30"),
            ("10:30", "11:30"),
            ("13:00", "14:00"),
            ("14:30", "15:00"),
            ("15:30", "16:30")
        ],
        "Thomas": [
            ("10:00", "12:00"),
            ("12:30", "13:00"),
            ("14:30", "16:00")
        ],
        "Jennifer": [
            ("9:00", "9:30"),
            ("10:00", "10:30"),
            ("11:00", "13:00"),
            ("13:30", "14:30"),
            ("15:00", "15:30"),
            ("16:00", "16:30")
        ]
    }

    # Convert busy times to minutes
    busy_minutes = {}
    for participant, intervals in participants_busy.items():
        converted = []
        for start_str, end_str in intervals:
            start_min = time_str_to_minutes(start_str)
            end_min = time_str_to_minutes(end_str)
            converted.append((start_min, end_min))
        busy_minutes[participant] = converted

    # Compute free intervals for each participant
    free_intervals = {}
    for participant, busy_list in busy_minutes.items():
        free_intervals[participant] = compute_free_intervals(busy_list, day_start, day_end)
    
    # Apply Wayne's constraint: avoid before 14:00 (840 minutes)
    wayne_free = free_intervals["Wayne"]
    wayne_constrained = []
    for start, end in wayne_free:
        low = max(start, 840)
        high = min(end, day_end)
        if low < high:
            wayne_constrained.append((low, high))
    free_intervals["Wayne"] = wayne_constrained

    # List of participants in order
    participant_names = ["Wayne", "Melissa", "Catherine", "Gregory", "Victoria", "Thomas", "Jennifer"]
    all_free = [free_intervals[name] for name in participant_names]
    
    # Compute common free intervals
    common = all_free[0]
    for i in range(1, len(all_free)):
        common = intersect_two_interval_lists(common, all_free[i])
        if not common:
            break
    
    # Find the first 30-minute slot
    meeting_start = None
    for start, end in common:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        print("No suitable time found")
        return
    
    meeting_end = meeting_start + meeting_duration
    start_h = meeting_start // 60
    start_m = meeting_start % 60
    end_h = meeting_end // 60
    end_m = meeting_end % 60
    
    print("Monday")
    print(f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}")

if __name__ == "__main__":
    main()