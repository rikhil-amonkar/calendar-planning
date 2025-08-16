import json
from datetime import datetime, timedelta

def calculate_meeting_schedule():
    # Define travel times
    travel_times = {
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Bayview"): 22,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Fisherman's Wharf"): 25
    }

    # Define meeting constraints
    meetings = {
        "Helen": {"location": "North Beach", "start": "7:00", "end": "16:45", "min_duration": 120},
        "Kimberly": {"location": "Fisherman's Wharf", "start": "16:30", "end": "21:00", "min_duration": 45},
        "Patricia": {"location": "Bayview", "start": "18:00", "end": "21:15", "min_duration": 120}
    }

    # Convert times to datetime objects
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M")

    # Check if a meeting can be scheduled
    def can_meet(start, end, min_duration):
        duration = (end - start).seconds // 60
        return duration >= min_duration

    # Calculate the best schedule
    def calculate_schedule():
        current_time = parse_time("9:00")
        current_location = "Nob Hill"
        itinerary = []

        # Sort meetings by start time
        sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]["start"]))

        for person, details in sorted_meetings:
            location = details["location"]
            start_time = parse_time(details["start"])
            end_time = parse_time(details["end"])
            min_duration = details["min_duration"]

            # Calculate travel time
            travel_time = travel_times[(current_location, location)]
            arrival_time = current_time + timedelta(minutes=travel_time)

            # Adjust meeting time if necessary
            if arrival_time < start_time:
                meeting_start = start_time
            else:
                meeting_start = arrival_time

            meeting_end = meeting_start + timedelta(minutes=min_duration)

            # Check if meeting can fit within available time
            if meeting_end <= end_time:
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": meeting_start.strftime("%H:%M"),
                    "end_time": meeting_end.strftime("%H:%M")
                })
                current_time = meeting_end
                current_location = location
            else:
                # If we can't fit the meeting, skip it
                continue

        return itinerary

    itinerary = calculate_schedule()
    return json.dumps({"itinerary": itinerary})

# Output the result
print(calculate_meeting_schedule())