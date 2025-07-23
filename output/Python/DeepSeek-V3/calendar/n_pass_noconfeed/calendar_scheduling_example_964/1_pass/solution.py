from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time_obj):
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return datetime.strptime(f"{hours:02d}:{mins:02d}", "%H:%M").time()

def get_available_slots(busy_slots, work_start, work_end, duration):
    available = []
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Sort busy slots by start time
    busy_slots.sort(key=lambda x: time_to_minutes(x[0]))
    
    prev_end = work_start_min
    for start, end in busy_slots:
        start_min = time_to_minutes(start)
        if start_min > prev_end:
            available.append((prev_end, start_min))
        prev_end = max(prev_end, time_to_minutes(end))
    
    if prev_end < work_end_min:
        available.append((prev_end, work_end_min))
    
    # Filter slots that can fit the duration
    valid_slots = []
    for start, end in available:
        if end - start >= duration:
            valid_slots.append((start, end))
    
    return valid_slots

def find_meeting_time(betty_busy, megan_busy, days, duration, work_start, work_end):
    work_start_time = parse_time(work_start)
    work_end_time = parse_time(work_end)
    duration_min = duration * 60
    
    for day in days:
        # Get Betty's busy slots for the day
        betty_day_busy = betty_busy.get(day, [])
        betty_slots = get_available_slots(betty_day_busy, work_start_time, work_end_time, duration_min)
        
        # Get Megan's busy slots for the day
        megan_day_busy = megan_busy.get(day, [])
        megan_slots = get_available_slots(megan_day_busy, work_start_time, work_end_time, duration_min)
        
        # Find overlapping slots
        for b_start, b_end in betty_slots:
            for m_start, m_end in megan_slots:
                overlap_start = max(b_start, m_start)
                overlap_end = min(b_end, m_end)
                if overlap_end - overlap_start >= duration_min:
                    start_time = minutes_to_time(overlap_start)
                    end_time = minutes_to_time(overlap_start + duration_min)
                    return day, start_time, end_time
    return None, None, None

def main():
    # Define work hours and meeting duration
    work_start = "09:00"
    work_end = "17:00"
    meeting_duration = 60  # minutes
    
    # Define days to check (excluding Wednesday and Thursday as per Betty's constraint)
    days_to_check = ["Monday", "Tuesday", "Friday"]
    
    # Define Betty's busy slots
    betty_busy = {
        "Monday": [
            (parse_time("10:00"), parse_time("10:30")),
            (parse_time("11:30"), parse_time("12:30")),
            (parse_time("16:00"), parse_time("16:30"))
        ],
        "Tuesday": [
            (parse_time("09:30"), parse_time("10:00")),
            (parse_time("10:30"), parse_time("11:00")),
            (parse_time("12:00"), parse_time("12:30")),
            (parse_time("13:30"), parse_time("15:00")),
            (parse_time("16:30"), parse_time("17:00"))
        ],
        "Friday": [
            (parse_time("09:00"), parse_time("10:00")),
            (parse_time("11:30"), parse_time("12:00")),
            (parse_time("12:30"), parse_time("13:00")),
            (parse_time("14:30"), parse_time("15:00"))
        ]
    }
    
    # Define Megan's busy slots
    megan_busy = {
        "Monday": [
            (parse_time("09:00"), parse_time("17:00"))
        ],
        "Tuesday": [
            (parse_time("09:00"), parse_time("09:30")),
            (parse_time("10:00"), parse_time("10:30")),
            (parse_time("12:00"), parse_time("14:00")),
            (parse_time("15:00"), parse_time("15:30")),
            (parse_time("16:00"), parse_time("16:30"))
        ],
        "Wednesday": [
            (parse_time("09:30"), parse_time("10:30")),
            (parse_time("11:00"), parse_time("11:30")),
            (parse_time("12:30"), parse_time("13:00")),
            (parse_time("13:30"), parse_time("14:30")),
            (parse_time("15:30"), parse_time("17:00"))
        ],
        "Thursday": [
            (parse_time("09:00"), parse_time("10:30")),
            (parse_time("11:30"), parse_time("14:00")),
            (parse_time("14:30"), parse_time("15:00")),
            (parse_time("15:30"), parse_time("16:30"))
        ],
        "Friday": [
            (parse_time("09:00"), parse_time("17:00"))
        ]
    }
    
    day, start_time, end_time = find_meeting_time(betty_busy, megan_busy, days_to_check, meeting_duration, work_start, work_end)
    
    if day and start_time and end_time:
        print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()