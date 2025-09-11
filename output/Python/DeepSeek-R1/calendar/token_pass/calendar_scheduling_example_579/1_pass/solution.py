def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Define constraints
    day = "Monday"
    meeting_duration = 30
    work_start = "9:00"
    work_end = "17:00"
    helen_cannot_after = "15:00"
    
    # Convert times to minutes since midnight
    start_min = time_to_minutes(work_start)
    end_min = time_to_minutes(helen_cannot_after)  # Effective end due to Helen's constraint
    cannot_after_min = time_to_minutes(helen_cannot_after)
    
    # Christine's meetings
    christine_busy = [
        ("11:00", "11:30"),
        ("15:00", "15:30")
    ]
    
    # Helen's blocked times
    helen_busy = [
        ("9:30", "10:30"),
        ("11:00", "11:30"),
        ("12:00", "12:30"),
        ("13:30", "16:00"),
        ("16:30", "17:00")
    ]
    
    # Convert busy times to minutes
    christine_busy_min = []
    for start, end in christine_busy:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        # Only consider busy times before cannot_after_min
        if s < cannot_after_min:
            christine_busy_min.append((s, e))
    
    helen_busy_min = []
    for start, end in helen_busy:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        # Adjust end time to cannot_after_min if necessary
        if e > cannot_after_min:
            e = cannot_after_min
        if s < cannot_after_min:
            helen_busy_min.append((s, e))
    
    # Find free intervals for Christine within [start_min, cannot_after_min]
    christine_free = []
    current = start_min
    for busy_start, busy_end in sorted(christine_busy_min, key=lambda x: x[0]):
        if current < busy_start:
            christine_free.append((current, busy_start))
        current = max(current, busy_end)
    if current < cannot_after_min:
        christine_free.append((current, cannot_after_min))
    
    # Find free intervals for Helen within [start_min, cannot_after_min]
    helen_free = []
    current = start_min
    for busy_start, busy_end in sorted(helen_busy_min, key=lambda x: x[0]):
        if current < busy_start:
            helen_free.append((current, busy_start))
        current = max(current, busy_end)
    if current < cannot_after_min:
        helen_free.append((current, cannot_after_min))
    
    # Find overlapping free intervals that are at least meeting_duration long
    for c_start, c_end in christine_free:
        for h_start, h_end in helen_free:
            overlap_start = max(c_start, h_start)
            overlap_end = min(c_end, h_end)
            if overlap_start < overlap_end and overlap_end - overlap_start >= meeting_duration:
                # Found a slot, output the first one
                meeting_start = overlap_start
                meeting_end = meeting_start + meeting_duration
                # Convert to time strings
                start_time_str = minutes_to_time(meeting_start)
                end_time_str = minutes_to_time(meeting_end)
                print(f"{start_time_str}:{end_time_str}")
                print(day)
                return
    
    # If no slot found, but problem says there is one
    print("No suitable time found")

if __name__ == "__main__":
    main()