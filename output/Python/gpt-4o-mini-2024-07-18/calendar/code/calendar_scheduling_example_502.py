from datetime import datetime, timedelta

# Participants' busy schedules in minutes from the start of the day (09:00)
jack_busy = [
    (30, 90),   # 09:30 to 10:30
    (90, 120),  # 11:00 to 11:30
    (150, 180), # 12:30 to 13:00
    (240, 270), # 14:00 to 14:30
    (300, 330)  # 16:00 to 16:30
]

charlotte_busy = [
    (30, 60),   # 09:30 to 10:00
    (60, 120),  # 10:30 to 12:00
    (150, 180), # 12:30 to 13:30
    (240, 360)  # 14:00 to 16:00
]

# Meeting duration in minutes
meeting_duration = 30
# Working hours
work_start = 9 * 60  # 09:00
work_end = 17 * 60    # 17:00

# Find available slots
def find_meeting_slot(jack_busy, charlotte_busy, meeting_duration, work_start, work_end):
    busy_times = sorted(jack_busy + charlotte_busy)
    available_times = []
    
    # Check before work_start
    if busy_times and busy_times[0][0] > work_start:
        available_times.append((work_start, busy_times[0][0]))
    
    # Check between busy times
    for i in range(len(busy_times) - 1):
        end_current = busy_times[i][1]
        start_next = busy_times[i+1][0]
        if start_next - end_current >= meeting_duration:
            available_times.append((end_current, start_next))
    
    # Check after last busy time
    if busy_times and busy_times[-1][1] < work_end:
        available_times.append((busy_times[-1][1], work_end))

    # Filter the slots based on the meeting duration
    for start, end in available_times:
        if end - start >= meeting_duration:
            return start, start + meeting_duration
    
    return None

# Get the meeting slot
meeting_slot = find_meeting_slot(jack_busy, charlotte_busy, meeting_duration, work_start, work_end)

# Convert to HH:MM
if meeting_slot:
    start_time = datetime.strptime(f"{work_start // 60}:{work_start % 60}", "%H:%M") + timedelta(minutes=meeting_slot[0])
    end_time = datetime.strptime(f"{work_end // 60}:{work_end % 60}", "%H:%M") + timedelta(minutes=meeting_slot[1])
    formatted_start = start_time.strftime("%H:%M")
    formatted_end = end_time.strftime("%H:%M")
    day_of_week = "Monday"
    
    print(f"{formatted_start}:{formatted_end}")
    print(day_of_week)