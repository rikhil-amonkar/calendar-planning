from datetime import datetime, timedelta

def find_meeting_time(amanda_schedule, nathan_schedule, meeting_duration, preferred_days, amanda_availability, nathan_availability):
    def parse_schedule(schedule):
        parsed = []
        for entry in schedule:
            start, end = entry.split('-')
            parsed.append((datetime.strptime(start, '%H:%M'), datetime.strptime(end, '%H:%M')))
        return parsed

    def is_time_within_availability(time, availability):
        for start, end in availability:
            if start <= time < end:
                return True
        return False

    def is_time_available(time, schedule):
        for start, end in schedule:
            if start <= time < end:
                return False
        return True

    def find_common_slot(amanda_slots, nathan_slots, duration, amanda_day_availability, nathan_day_availability):
        for amanda_start, amanda_end in amanda_slots:
            current = amanda_start
            while current + timedelta(minutes=duration) <= amanda_end:
                if (is_time_available(current, nathan_slots) and
                    is_time_within_availability(current, nathan_day_availability) and
                    is_time_within_availability(current + timedelta(minutes=duration), nathan_day_availability)):
                    return current, current + timedelta(minutes=duration)
                current += timedelta(minutes=5)
        return None, None

    amanda_schedule = parse_schedule(amanda_schedule)
    nathan_schedule = parse_schedule(nathan_schedule)

    for day in preferred_days:
        amanda_day_availability = amanda_availability.get(day, [])
        nathan_day_availability = nathan_availability.get(day, [])

        # Filter out slots that are outside of their daily availability
        amanda_slots = [(start, end) for start, end in amanda_schedule if is_time_within_availability(start, amanda_day_availability) and is_time_within_availability(end, amanda_day_availability)]
        nathan_slots = [(start, end) for start, end in nathan_schedule if is_time_within_availability(start, nathan_day_availability) and is_time_within_availability(end, nathan_day_availability)]

        meeting_start, meeting_end = find_common_slot(amanda_slots, nathan_slots, meeting_duration, amanda_day_availability, nathan_day_availability)
        if meeting_start and meeting_end:
            return meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'), day

    return None, None, None

# Define schedules and constraints
amanda_schedule = ["9:00-10:30", "11:00-11:30", "12:30-13:00", "13:30-14:00", "14:30-15:00"]
nathan_schedule = ["10:00-10:30", "11:00-11:30", "13:30-14:30", "16:00-16:30", "9:00-10:30", "11:00-13:00", "13:30-14:00", "14:30-15:30", "16:00-16:30"]

meeting_duration = 30  # in minutes
preferred_days = ["Monday", "Tuesday"]

amanda_availability = {
    "Monday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("11:00", "%H:%M"))]
}

nathan_availability = {
    "Monday": [],
    "Tuesday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

meeting_start, meeting_end, day = find_meeting_time(amanda_schedule, nathan_schedule, meeting_duration, preferred_days, amanda_availability, nathan_availability)
print(f"{meeting_start} {meeting_end} {day}")