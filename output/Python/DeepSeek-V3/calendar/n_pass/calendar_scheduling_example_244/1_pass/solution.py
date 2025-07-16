def find_meeting_time(participants_schedules, duration_minutes, work_hours_start, work_hours_end):
    # Convert all times to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert work hours to minutes
    start_min = time_to_minutes(work_hours_start)
    end_min = time_to_minutes(work_hours_end)

    # Initialize a list to keep track of busy intervals for all participants
    all_busy_intervals = []

    for schedule in participants_schedules:
        for busy_start, busy_end in schedule:
            all_busy_intervals.append((time_to_minutes(busy_start), time_to_minutes(busy_end)))

    # Sort all busy intervals by start time
    all_busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged_intervals = []
    for start, end in all_busy_intervals:
        if not merged_intervals:
            merged_intervals.append([start, end])
        else:
            last_start, last_end = merged_intervals[-1]
            if start <= last_end:
                # Overlapping or adjacent intervals, merge them
                merged_intervals[-1][1] = max(end, last_end)
            else:
                merged_intervals.append([start, end])

    # Find available slots by checking gaps between merged intervals and work hours
    available_slots = []
    previous_end = start_min

    for start, end in merged_intervals:
        if start > previous_end:
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)

    # Check the time after the last busy interval until work hours end
    if previous_end < end_min:
        available_slots.append((previous_end, end_min))

    # Find the first available slot that can fit the meeting duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return meeting_start, meeting_end

    return None, None

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' schedules
participants_schedules = [
    [],  # Walter has no meetings
    [("09:00", "09:30"), ("10:00", "10:30"), ("13:30", "14:30"), ("15:00", "16:00")],  # Cynthia
    [("10:00", "11:00"), ("13:00", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],  # Ann
    [("09:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],  # Catherine
    [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:30"), ("15:00", "16:00")],  # Kyle
]

# Meeting duration in minutes
duration_minutes = 30

# Work hours
work_hours_start = "09:00"
work_hours_end = "17:00"

# Find meeting time
meeting_start, meeting_end = find_meeting_time(participants_schedules, duration_minutes, work_hours_start, work_hours_end)

if meeting_start is not None:
    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_end)
    print(f"{start_time}:{end_time}")
    print("Monday")
else:
    print("No available time slot found.")