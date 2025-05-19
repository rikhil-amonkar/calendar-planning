def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours and constraints
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30
bobby_limit = time_to_minutes("15:00")

# Define busy intervals in minutes
busy = {
    'Lisa': [
        (time_to_minutes("9:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    'Bobby': [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    'Randy': [
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Find first valid slot
for start in range(work_start, bobby_limit - meeting_duration + 1):
    end = start + meeting_duration
    # Check Bobby's after-15:00 constraint
    if end > bobby_limit:
        continue
    # Check all participants' availability
    valid = True
    for person, intervals in busy.items():
        for (s, e) in intervals:
            if not (end <= s or start >= e):
                valid = False
                break
        if not valid:
            break
    if valid:
        print(f"Monday {minutes_to_time(start)}:{minutes_to_time(end)}")
        exit()

# Fallback if no slot found (though problem states solution exists)
print("No valid slot found")