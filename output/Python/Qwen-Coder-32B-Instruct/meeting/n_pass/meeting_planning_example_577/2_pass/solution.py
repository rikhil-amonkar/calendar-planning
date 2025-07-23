import json
from datetime import datetime, timedelta

# Define the travel times
travel_times = {
    "Haight-Ashbury": {"Russian Hill": 17, "Fisherman's Wharf": 23, "Nob Hill": 15, "Golden Gate Park": 7, "Alamo Square": 5, "Pacific Heights": 12},
    "Russian Hill": {"Haight-Ashbury": 17, "Fisherman's Wharf": 7, "Nob Hill": 5, "Golden Gate Park": 21, "Alamo Square": 15, "Pacific Heights": 7},
    "Fisherman's Wharf": {"Haight-Ashbury": 22, "Russian Hill": 7, "Nob Hill": 11, "Golden Gate Park": 25, "Alamo Square": 20, "Pacific Heights": 12},
    "Nob Hill": {"Haight-Ashbury": 13, "Russian Hill": 5, "Fisherman's Wharf": 11, "Golden Gate Park": 17, "Alamo Square": 11, "Pacific Heights": 8},
    "Golden Gate Park": {"Haight-Ashbury": 7, "Russian Hill": 19, "Fisherman's Wharf": 24, "Nob Hill": 20, "Alamo Square": 10, "Pacific Heights": 16},
    "Alamo Square": {"Haight-Ashbury": 5, "Russian Hill": 13, "Fisherman's Wharf": 19, "Nob Hill": 11, "Golden Gate Park": 9, "Pacific Heights": 10},
    "Pacific Heights": {"Haight-Ashbury": 11, "Russian Hill": 7, "Fisherman's Wharf": 13, "Nob Hill": 8, "Golden Gate Park": 15, "Alamo Square": 10}
}

# Define the constraints
constraints = {
    "Stephanie": {"location": "Russian Hill", "start": "20:00", "end": "20:45", "min_duration": 15},
    "Kevin": {"location": "Fisherman's Wharf", "start": "19:15", "end": "21:45", "min_duration": 75},
    "Robert": {"location": "Nob Hill", "start": "07:45", "end": "10:30", "min_duration": 90},
    "Steven": {"location": "Golden Gate Park", "start": "08:30", "end": "17:00", "min_duration": 75},
    "Anthony": {"location": "Alamo Square", "start": "07:45", "end": "19:45", "min_duration": 15},
    "Sandra": {"location": "Pacific Heights", "start": "14:45", "end": "21:45", "min_duration": 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_to_str(time_obj):
    return time_obj.strftime("%H:%M")

def find_meeting_schedule(constraints, travel_times):
    current_time = parse_time("09:00")
    current_location = "Haight-Ashbury"
    itinerary = []

    def can_meet(person, start_time, end_time, min_duration):
        available_time = (end_time - start_time).seconds // 60
        return available_time >= min_duration

    while current_time < parse_time("21:45"):
        possible_meetings = []
        for person, details in constraints.items():
            start = parse_time(details["start"])
            end = parse_time(details["end"])
            min_duration = details["min_duration"]
            location = details["location"]

            if current_time <= start and can_meet(person, start, end, min_duration):
                travel_time = travel_times[current_location][location]
                arrival_time = current_time + timedelta(minutes=travel_time)
                meeting_start = max(arrival_time, start)
                meeting_end = min(meeting_start + timedelta(minutes=min_duration), end)

                if meeting_start + timedelta(minutes=min_duration) <= end:
                    possible_meetings.append({
                        "person": person,
                        "location": location,
                        "start": meeting_start,
                        "end": meeting_end,
                        "travel_time": travel_time
                    })

        if possible_meetings:
            # Sort meetings by latest possible end time
            possible_meetings.sort(key=lambda x: x["end"], reverse=True)
            best_meeting = possible_meetings[0]

            # Ensure the meeting starts after the current time plus travel time
            if best_meeting["start"] >= current_time + timedelta(minutes=best_meeting["travel_time"]):
                # Update current time and location
                current_time = best_meeting["end"]
                current_location = best_meeting["location"]

                # Add to itinerary
                itinerary.append({
                    "action": "meet",
                    "location": best_meeting["location"],
                    "person": best_meeting["person"],
                    "start_time": time_to_str(best_meeting["start"]),
                    "end_time": time_to_str(best_meeting["end"])
                })
            else:
                # If the meeting cannot be scheduled due to travel time, skip it
                continue
        else:
            break

    return itinerary

itinerary = find_meeting_schedule(constraints, travel_times)
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))