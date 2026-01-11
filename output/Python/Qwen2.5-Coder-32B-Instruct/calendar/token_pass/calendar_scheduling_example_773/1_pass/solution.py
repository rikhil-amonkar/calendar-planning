# Define the working hours
start_time = 9  # 9:00 AM
end_time = 17   # 5:00 PM

# Roy's busy times
roy_busy_times = {
    'Monday': [(10, 11.5), (12, 13), (14, 14.5), (15, 17)],
    'Tuesday': [(10.5, 11.5), (12, 14.5), (15, 15.5), (16, 17)],
    'Wednesday': [(9.5, 11.5), (12.5, 14), (14.5, 15.5), (16.5, 17)]
}

def is_time_slot_free(day, start):
    """Check if the time slot from start to start+1 is free for Roy."""
    for busy_start, busy_end in roy_busy_times[day]:
        if busy_start <= start < busy_end or busy_start < start + 1 <= busy_end:
            return False
    return True

def find_meeting_time():
    """Find the earliest available meeting time for Patrick and Roy."""
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        for hour in range(start_time, end_time):
            if is_time_slot_free(day, hour):
                # Convert hour to HH:MM format
                start_formatted = f"{int(hour):02}:{int((hour % 1) * 60):02}"
                end_formatted = f"{int(hour + 1):02}:{int(((hour + 1) % 1) * 60):02}"
                return f"{start_formatted}:{end_formatted} {day}"

meeting_time = find_meeting_time()
print(meeting_time)