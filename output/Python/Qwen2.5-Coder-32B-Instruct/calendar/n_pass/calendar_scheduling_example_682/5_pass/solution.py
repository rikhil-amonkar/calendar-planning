from datetime import datetime, timedelta

def find_meeting_time(amanda_schedule, nathan_schedule, meeting_duration, preferred_days, amanda_availability, nathan_availability):
    def parse_schedule(schedule, day_availability):
        parsed = []
        for entry in schedule:
            start, end = entry.split('-')
            start_time = datetime.strptime(start, '%H:%M').time()
            end_time = datetime.strptime(end, '%H:%M').time()
            for avail_start, avail_end in day_availability:
                avail_start_time = avail_start.time()
                avail_end_time = avail_end.time()
                if avail_start_time <= start_time < avail_end_time and avail_start_time <= end_time < avail_end_time:
                    parsed.append((datetime.combine(avail_start.date(), start_time), datetime.combine(avail_start.date(), end_time)))
        return parsed

    def is_time_available(time, schedule):
        for start, end in schedule:
            if start <= time < end:
                return True
        return False

    def find_common_slot(amanda_slots, nathan_slots, duration):
        for amanda_start, amanda_end in amanda_slots:
            current = amanda_start
            while current + timedelta(minutes=duration) <= amanda_end:
                if is_time_available(current, nathan_slots):
                    return current, current + timedelta(minutes=duration)
                current += timedelta(minutes=5)
        return None, None

    for day in preferred_days:
        amanda_day_availability = amanda_availability.get(day, [])
        nathan_day_availability = nathan_availability.get(day, [])

        # Filter out slots that are outside of their daily availability
        amanda_slots = [slot for slot in parse_schedule(amanda_schedule, amanda_day_availability) if any(is_time_available(slot[0], [avail]) and is_time_available(slot[1], [avail]) for avail in amanda_day_availability)]
        nathan_slots = [slot for slot in parse_schedule(nathan_schedule, nathan_day_availability) if any(is_time_available(slot[0], [avail]) and is_time_available(slot[1], [avail]) for avail in nathan_day_availability)]

        meeting_start, meeting_end = find_common_slot(amanda_slots, nathan_slots, meeting_duration)
        if meeting_start and meeting_end:
            return meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'), day

    return None, None, None

# Define schedules and constraints
amanda_schedule = ["9:00-10:30", "11:00-11:30", "12:30-13:00", "13:30-14:30", "14:30-15:00"]
nathan_schedule = ["10:00-10:30", "11:00-11:30", "13:30-14:30", "16:00-16:30", "9:00-10:30", "11:00-13:00", "13:30-14:00", "14:30-15:30", "16:00-16:30"]

meeting_duration = 30  # in minutes
preferred_days = ["Monday", "Tuesday"]

amanda_availability = {
    "Monday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("11:00", "%H:%M"))]
}

nathan_availability = {
    "Monday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("12:00", "%H:%M"))],  # Adjusted availability
    "Tuesday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

meeting_start, meeting_end, day = find_meeting_time(amanda_schedule, nathan_schedule, meeting_duration, preferred_days, amanda_availability, nathan_availability)
print(f"{meeting_start} {meeting_end} {day}")