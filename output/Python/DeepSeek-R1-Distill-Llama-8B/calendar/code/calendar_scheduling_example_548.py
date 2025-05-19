from datetime import time as Time

def find_meeting_time():
    # Define the participants and their schedules
    participants = {
        'Judy': ('09:00', '17:00'),
        'Nicole': (
            ('09:00', '10:00'),
            ('10:30', '16:30')
        )
    }

    # Convert time strings to minutes since 09:00
    def to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Convert each participant's schedule to a list of busy intervals
    busy_times = {}
    for name, schedule in participants.items():
        times = []
        for start, end in schedule:
            start_min = to_minutes(start)
            end_min = to_minutes(end)
            times.append((start_min, end_min))
        busy_times[name] = times

    # Function to check if a time is busy for a participant
    def is_busy(name, time_min):
        for start, end in busy_times[name]:
            if start <= time_min < end:
                return True
        return False

    # The meeting duration is 30 minutes
    duration = 30

    # Nicole prefers not to meet before 16:00
    preferred_start = 16 * 60

    # Iterate through possible start times from 09:00 to 16:30
    for start_h in range(9, 17):
        for start_m in range(0, 60):
            current_time = start_h * 60 + start_m
            end_time = current_time + duration

            # Check if end_time is within the day (09:00 to 17:00)
            if end_time >= 17 * 60:
                continue

            # Check if both participants are free at current_time
            if not is_busy('Judy', current_time) and not is_busy('Nicole', current_time):
                # Format the time and return
                return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d} Monday"

    # If no slot found (though problem states a solution exists)
    return "No suitable time found"

# Run the function and print the result
print(find_meeting_time())