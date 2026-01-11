# Define the busy times for each participant in minutes since 9:00
busy_times = {
    'Joe': [(30, 60), (90, 120)],  # 9:30-10:00, 10:30-11:00
    'Keith': [(150, 180), (360, 390)],  # 11:30-12:00, 15:00-15:30
    'Patricia': [(0, 30), (240, 270)],  # 9:00-9:30, 13:00-13:30
    'Nancy': [(0, 120), (150, 450)],  # 9:00-11:00, 11:30-16:30
    'Pamela': [(0, 60), (90, 120), (150, 180), (240, 270), (270, 300), (360, 390), (450, 480)]  # 9:00-10:00, 10:30-11:00, 11:30-12:30, 13:00-14:00, 14:30-15:00, 15:30-16:00, 16:30-17:00
}

def convert_minutes_to_time(minutes):
    """Converts minutes since 9:00 to HH:MM format."""
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Check each 30-minute slot from 0 to 480 minutes (9:00 to 16:30)
for start in range(0, 480 - 30 + 1, 30):  # Step by 30 minutes
    end = start + 30
    # Check if this slot is free for all participants
    slot_free = True
    for person, times in busy_times.items():
        for busy_start, busy_end in times:
            if start < busy_end and end > busy_start:
                slot_free = False
                break
        if not slot_free:
            break
    if slot_free:
        # Found a free slot, print it and exit
        start_time = convert_minutes_to_time(start)
        end_time = convert_minutes_to_time(end)
        print(f"Meeting time: {start_time}-{end_time} on Monday")
        break