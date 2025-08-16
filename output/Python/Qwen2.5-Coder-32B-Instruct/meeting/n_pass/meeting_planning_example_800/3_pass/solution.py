import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Union Square", "Central Park"): 10,
    ("Union Square", "Brooklyn Bridge"): 20,
    ("Union Square", "Times Square"): 5,
    ("Central Park", "Brooklyn Bridge"): 15,
    ("Central Park", "Times Square"): 10,
    ("Brooklyn Bridge", "Times Square"): 10,
}

# Define meeting constraints
meetings = {
    "Person A": {"start": "10:00", "end": "11:00", "min_duration": 30, "location": "Central Park"},
    "Person B": {"start": "10:30", "end": "11:30", "min_duration": 20, "location": "Brooklyn Bridge"},
    "Person C": {"start": "11:00", "end": "12:00", "min_duration": 40, "location": "Times Square"},
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_optimal_schedule(start_time, meetings, travel_times):
    def can_meet(meeting, current_time):
        meeting_start = parse_time(meeting["start"])
        meeting_end = parse_time(meeting["end"])
        return meeting_start <= current_time <= meeting_end - timedelta(minutes=meeting["min_duration"])

    def next_location(current_location, current_time, remaining_meetings):
        best_schedule = None
        best_time = timedelta(hours=23, minutes=59)

        for person, meeting in remaining_meetings.items():
            location = meeting["location"]
            if can_meet(meeting, current_time):
                travel_time = travel_times.get((current_location, location), float('inf'))
                new_time = current_time + timedelta(minutes=travel_time)
                if new_time + timedelta(minutes=meeting["min_duration"]) <= parse_time(meeting["end"]):
                    schedule = [{"action": "travel", "location": location, "start_time": time_to_str(current_time), "end_time": time_to_str(new_time)}]
                    schedule.append({"action": "meet", "location": location, "person": person, "start_time": time_to_str(new_time), "end_time": time_to_str(new_time + timedelta(minutes=meeting["min_duration"]))})
                    remaining = remaining_meetings.copy()
                    del remaining[person]
                    next_sched, next_time = next_location(location, new_time + timedelta(minutes=meeting["min_duration"]), remaining)
                    if next_sched is not None:
                        schedule.extend(next_sched)
                        total_time = next_time - current_time
                        if total_time < best_time:
                            best_schedule = schedule
                            best_time = total_time

        if best_schedule is None:
            # If no better schedule found, return an empty schedule with the current time
            return [], current_time
        return best_schedule, best_time

    start_location = "Union Square"
    itinerary, _ = next_location(start_location, parse_time(start_time), meetings)
    return itinerary

start_time = "09:00"
optimal_itinerary = find_optimal_schedule(start_time, meetings, travel_times)

# Format the output as JSON
output = {
    "itinerary": optimal_itinerary
}

print(json.dumps(output, indent=2))