def find_meeting_time():
    # Define the work hours as a list of possible time slots in minutes
    work_hours = {
        "start": 9 * 60,  # 9:00 in minutes
        "end": 17 * 60    # 17:00 in minutes
    }

    # Participants' schedules in minutes
    participants = {
        "Emily": [
            (10*60, 10*60 + 30),     # 10:00-10:30
            (11*60 + 30, 12*60 + 30),# 11:30-12:30
            (14*60, 15*60),          # 14:00-15:00
            (16*60, 16*60 + 30)      # 16:00-16:30
        ],
        "Melissa": [
            (9*60 + 30, 10*60),      # 9:30-10:00
            (14*60 + 30, 15*60)      # 14:30-15:00
        ],
        "Frank": [
            (10*60, 10*60 + 30),     # 10:00-10:30
            (11*60, 11*60 + 30),     # 11:00-11:30
            (12*60 + 30, 13*60),     # 12:30-13:00
            (13*60 + 30, 14*60 + 30),# 13:30-14:30
            (15*60, 16*60),          # 15:00-16:00
            (16*60 + 30, 17*60)      # 16:30-17:00
        ]
    }

    # Frank's preference: no meetings after 9:30
    frank_preference = 9*60 + 30  # 9:30 in minutes

    # Convert time in minutes to HH:MM format
    def minutes_to_time(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"

    # Check each 30-minute slot within work hours, considering Frank's preference
    for hour in range(work_hours["start"], work_hours["end"] + 1):
        for minute in [0, 30]:
            start = hour * 60 + minute
            end = start + 30

            # Skip if the slot goes beyond work hours or after Frank's preferred time
            if end > work_hours["end"] * 60 or start >= frank_preference:
                continue

            # Check availability for all participants
            is_available = True
            for name, schedule in participants.items():
                for busy_start, busy_end in schedule:
                    # Check if the current slot overlaps with any busy time
                    if not (end <= busy_start or start >= busy_end):
                        is_available = False
                        break
                if not is_available:
                    break

            if is_available:
                # Convert to HH:MM format
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                return f"{start_time}:{end_time}"

    return "No available time found"

# Execute the function
meeting_time = find_meeting_time()
print(f"The proposed meeting time is {meeting_time} on Monday.")