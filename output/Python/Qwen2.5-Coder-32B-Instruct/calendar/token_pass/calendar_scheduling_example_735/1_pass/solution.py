def find_meeting_time(ronald_schedule, amber_schedule, days, meeting_duration):
    # Define the time slots from 9:00 to 17:00 in 30-minute increments
    start_hour = 9
    end_hour = 17
    time_slots = []
    for day in days:
        current_hour = start_hour
        while current_hour < end_hour:
            time_slots.append((day, current_hour, current_hour + meeting_duration))
            if current_hour + meeting_duration + 0.5 <= end_hour:
                time_slots.append((day, current_hour + 0.5, current_hour + meeting_duration + 0.5))
            current_hour += 1

    # Convert blocked times into a list of tuples (start, end)
    def parse_blocked_times(schedule):
        blocked_times = []
        for entry in schedule:
            parts = entry.split()
            day = parts[0]
            times = parts[1].split(',')
            for time_range in times:
                start_end = time_range.split('-')
                start = int(start_end[0].split(':')[0]) + int(start_end[0].split(':')[1]) / 60
                end = int(start_end[1].split(':')[0]) + int(start_end[1].split(':')[1]) / 60
                blocked_times.append((day, start, end))
        return blocked_times

    ronald_blocked = parse_blocked_times(ronald_schedule)
    amber_blocked = parse_blocked_times(amber_schedule)

    # Check for available slots
    for slot in time_slots:
        day, start, end = slot
        available = True
        for blocked in ronald_blocked + amber_blocked:
            if day == blocked[0] and not (end <= blocked[1] or start >= blocked[2]):
                available = False
                break
        if available:
            start_time_str = f"{int(start):02}:{int((start % 1) * 60):02}"
            end_time_str = f"{int(end):02}:{int((end % 1) * 60):02}"
            return f"{start_time_str}:{end_time_str} {day}"

# Input data
ronald_schedule = ["Monday 10:30-11:00,12:00-12:30,15:30-16:00",
                   "Tuesday 9:00-9:30,12:00-12:30,15:30-16:30",
                   "Wednesday 9:30-10:30,11:00-12:00,12:30-13:00,13:30-14:00,16:30-17:00"]
amber_schedule = ["Monday 9:00-9:30,10:00-10:30,11:30-12:00,12:30-14:00,14:30-15:00,15:30-17:00",
                  "Tuesday 9:00-9:30,10:00-11:30,12:00-12:30,13:30-15:30,16:30-17:00",
                  "Wednesday 9:00-9:30,10:00-10:30,11:00-13:30,15:00-15:30"]
days = ["Monday", "Tuesday", "Wednesday"]
meeting_duration = 0.5  # 30 minutes

# Find and print the meeting time
meeting_time = find_meeting_time(ronald_schedule, amber_schedule, days, meeting_duration)
print(meeting_time)