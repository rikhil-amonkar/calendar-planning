# Define busy intervals for each participant in minutes since midnight
participants_busy = {
    'Tyler': [],
    'Kelly': [],
    'Stephanie': [(660, 690), (870, 900)],
    'Hannah': [],
    'Joe': [(540, 570), (600, 720), (750, 780), (840, 1020)],
    'Diana': [(540, 630), (690, 720), (780, 840), (870, 930), (960, 1020)],
    'Deborah': [(540, 600), (630, 720), (750, 780), (810, 840), (870, 930), (960, 990)]
}

# Iterate through all possible start times from 9:00 (540) to 16:30 (990)
for start_time in range(540, 990 + 1):
    end_time = start_time + 30
    # Check if the slot is within work hours (up to 17:00)
    if end_time > 1020:
        continue
    # Assume the slot is valid until proven otherwise
    valid = True
    # Check against all participants' busy intervals
    for busy_intervals in participants_busy.values():
        for b_start, b_end in busy_intervals:
            # Check if there's an overlap
            if not (end_time <= b_start or start_time >= b_end):
                valid = False
                break
        if not valid:
            break
    if valid:
        # Convert start and end times to HH:MM format
        start_h = start_time // 60
        start_m = start_time % 60
        end_h = end_time // 60
        end_m = end_time % 60
        time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
        day_str = "Monday"
        print(f"{time_str} {day_str}")
        exit()

# If no slot found (though problem states there is one)
print("No suitable time found.")