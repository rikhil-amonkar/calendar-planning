def main():
    # Meeting duration and work hours
    meeting_duration = 30  # minutes
    work_start = 9 * 60  # 9:00 in minutes (from midnight)
    work_end = 17 * 60   # 17:00 in minutes

    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    # Convert minutes since midnight back to HH:MM format
    def minutes_to_time(total_minutes):
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Participants' busy intervals (each interval is [start_minute, end_minute])
    bradley_busy = [
        ("9:30", "10:00"),
        ("12:30", "13:00"),
        ("13:30", "14:00"),
        ("15:30", "16:00")
    ]
    teresa_busy = [
        ("10:30", "11:00"),
        ("12:00", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00")
    ]
    elizabeth_busy = [
        ("9:00", "9:30"),
        ("10:30", "11:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00"),
        ("15:30", "17:00")
    ]
    christian_busy = [
        ("9:00", "9:30"),
        ("10:30", "17:00")
    ]

    # Combine all busy intervals into a list of (start, end) in minutes
    all_busy = []
    for intervals in [bradley_busy, teresa_busy, elizabeth_busy, christian_busy]:
        for start_str, end_str in intervals:
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            all_busy.append((start_min, end_min))

    # Create a timeline for the work day (in minutes)
    timeline = [0] * (work_end + 1)  # Index represents minutes from 00:00
    # Mark work hours as available (1), but we'll mark busy times separately
    for start, end in all_busy:
        # Clamp the interval to the work day
        start_clamp = max(start, work_start)
        end_clamp = min(end, work_end)
        # Mark each minute in the busy interval as unavailable (0)
        for minute in range(start_clamp, end_clamp):
            if minute <= work_end:
                timeline[minute] = 1  # Mark as busy

    # Find available slots (consecutive free minutes)
    available_slots = []
    in_slot = False
    slot_start = work_start
    for minute in range(work_start, work_end):
        if timeline[minute] == 0:  # Free minute
            if not in_slot:
                in_slot = True
                slot_start = minute
        else:  # Busy minute
            if in_slot:
                in_slot = False
                slot_end = minute
                available_slots.append((slot_start, slot_end))
    if in_slot:
        available_slots.append((slot_start, work_end))

    # Find first available slot that fits the meeting duration
    meeting_time = None
    for start, end in available_slots:
        duration = end - start
        if duration >= meeting_duration:
            meeting_time = (start, start + meeting_duration)
            break

    if meeting_time:
        start_time = minutes_to_time(meeting_time[0])
        end_time = minutes_to_time(meeting_time[1])
        print(f"{start_time}:{end_time}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()