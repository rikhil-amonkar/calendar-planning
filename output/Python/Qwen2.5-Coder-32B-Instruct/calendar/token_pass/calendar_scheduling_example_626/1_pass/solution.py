def find_meeting_time(patricia_schedule, jesse_schedule, meeting_duration=1, days=['Monday', 'Tuesday']):
    # Convert time strings to minutes since start of the day for easier comparison
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    # Generate all possible time slots for a day
    def generate_time_slots(start_time, end_time, duration):
        start_minutes = time_to_minutes(start_time)
        end_minutes = time_to_minutes(end_time)
        slots = []
        current = start_minutes
        while current + duration <= end_minutes:
            slots.append((current, current + duration))
            current += 60  # Increment by one hour
        return slots

    # Remove busy slots from available slots
    def remove_busy_slots(available_slots, busy_slots):
        busy_set = set(busy_slots)
        return [slot for slot in available_slots if slot not in busy_set]

    # Main logic
    start_time = "09:00"
    end_time = "17:00"

    # Generate all possible time slots for each day
    all_slots = generate_time_slots(start_time, end_time, meeting_duration * 60)

    # Convert busy times to minute format
    patricia_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in patricia_schedule]
    jesse_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in jesse_schedule]

    # Iterate over each day
    for day in days:
        # Filter out busy slots for Patricia and Jesse
        patricia_free = remove_busy_slots(all_slots, patricia_busy)
        jesse_free = remove_busy_slots(all_slots, jesse_busy)

        # Find common free slots
        common_free_slots = set(patricia_free) & set(jesse_free)

        # Check for any common free slot
        for slot in common_free_slots:
            start, end = slot
            print(f"{minutes_to_time(start)}:{minutes_to_time(end)} {day}")
            return  # Return the first valid slot found

# Define schedules
patricia_schedule = [("10:00", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "16:30"),
                     ("10:00", "10:30"), ("11:00", "12:00"), ("14:00", "16:00"), ("16:30", "17:00")]

jesse_schedule = [("9:00", "17:00"),
                  ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")]

# Find and print the meeting time
find_meeting_time(patricia_schedule, jesse_schedule)