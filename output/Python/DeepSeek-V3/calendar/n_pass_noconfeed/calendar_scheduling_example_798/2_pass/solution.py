def find_meeting_time(nancy_schedule, jose_schedule, days, work_hours, duration):
    start_work, end_work = work_hours
    duration_minutes = duration
    
    for day in days:
        # Get busy intervals for Nancy and Jose on the current day
        nancy_busy = nancy_schedule.get(day, [])
        jose_busy = jose_schedule.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = nancy_busy + jose_busy
        all_busy.sort()
        
        # Initialize previous end time to start of work day
        prev_end = start_work
        
        # Iterate through all busy intervals to find gaps
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                # Found a gap, check if it's long enough
                gap_start = prev_end
                gap_end = busy_start
                if (gap_end - gap_start) >= duration_minutes:
                    return day, (gap_start, gap_start + duration_minutes)
            # Update previous end time to the end of the current busy interval
            prev_end = max(prev_end, busy_end)
        
        # Check the gap after the last busy interval until end of work day
        if (end_work - prev_end) >= duration_minutes:
            return day, (prev_end, prev_end + duration_minutes)
    
    return None, None

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define more realistic schedules with actual availability
nancy_schedule = {
    "Monday": [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30"))
    ],
    "Tuesday": [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30"))
    ],
    "Wednesday": [
        (time_to_minutes("10:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:30"))
    ]
}

jose_schedule = {
    "Monday": [
        (time_to_minutes("09:00"), time_to_minutes("10:15")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("15:00"), time_to_minutes("16:00"))
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ],
    "Wednesday": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ]
}

days_to_check = ["Monday", "Tuesday", "Wednesday"]
work_hours = (time_to_minutes("09:00"), time_to_minutes("17:00"))
meeting_duration = 30  # in minutes

day, time_slot = find_meeting_time(nancy_schedule, jose_schedule, days_to_check, work_hours, meeting_duration)

if day and time_slot:
    start_time, end_time = time_slot
    print(f"Available meeting time:")
    print(f"{day}: {minutes_to_time(start_time)} to {minutes_to_time(end_time)}")
else:
    print("No suitable meeting time found.")