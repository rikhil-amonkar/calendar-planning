def time_to_minutes(time_str):
    # Converts HH:MM into minutes past midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Converts minutes past midnight into HH:MM string with leading zeros.
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def get_free_intervals(busy_times, work_start, work_end):
    # Given busy intervals (as tuples of "HH:MM" strings),
    # return a sorted list of free intervals as (start_minutes, end_minutes) within work hours.
    busy = sorted([(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_times])
    free = []
    current = work_start
    for start, end in busy:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_earliest_slot(arthur_free, michael_free, duration):
    # Find the earliest overlapping free interval (from Arthur and Michael)
    # that is at least 'duration' minutes long. Returns a tuple (start, start+duration).
    earliest = None
    for a_start, a_end in arthur_free:
        for m_start, m_end in michael_free:
            slot_start = max(a_start, m_start)
            slot_end = min(a_end, m_end)
            if slot_end - slot_start >= duration:
                if earliest is None or slot_start < earliest[0]:
                    earliest = (slot_start, slot_start + duration)
    return earliest

def main():
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Define the schedules as provided:
    schedules = {
        "Arthur": {
            "Monday": [("11:00", "11:30"), ("13:30", "14:00"), ("15:00", "15:30")],
            "Tuesday": [("13:00", "13:30"), ("16:00", "16:30")],
            "Wednesday": [("10:00", "10:30"), ("11:00", "11:30"),
                          ("12:00", "12:30"), ("14:00", "14:30"),
                          ("16:00", "16:30")]
        },
        "Michael": {
            "Monday": [("09:00", "12:00"), ("12:30", "13:00"),
                       ("14:00", "14:30"), ("15:00", "17:00")],
            "Tuesday": [("09:30", "11:30"), ("12:00", "13:30"),
                        ("14:00", "15:30")],
            "Wednesday": [("10:00", "12:30"), ("13:00", "13:30")]
        }
    }
    
    # Constraint: Arthur cannot meet on Tuesday.
    allowed_days = ["Monday", "Wednesday"]
    
    proposed_day = None
    proposed_slot = None
    
    # Loop over allowed days in order (earliest availability):
    for day in allowed_days:
        # Get the busy intervals for the day (or empty list if none)
        arthur_busy = schedules["Arthur"].get(day, [])
        michael_busy = schedules["Michael"].get(day, [])
        
        # Calculate free intervals during work hours
        arthur_free = get_free_intervals(arthur_busy, work_start, work_end)
        michael_free = get_free_intervals(michael_busy, work_start, work_end)
        
        # Find earliest overlapping free slot that fits the meeting duration
        slot = find_earliest_slot(arthur_free, michael_free, meeting_duration)
        if slot:
            proposed_day = day
            proposed_slot = slot
            break
    
    if proposed_day and proposed_slot:
        start_str = minutes_to_time(proposed_slot[0])
        end_str = minutes_to_time(proposed_slot[1])
        # Output in the required format: Day followed by the time range in HH:MM:HH:MM format 
        print(f"{proposed_day} {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()