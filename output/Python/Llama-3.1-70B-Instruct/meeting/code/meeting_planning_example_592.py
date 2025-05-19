import json

def calculate_travel_time(origin, destination, travel_times):
    return travel_times.get((origin, destination), 0)

def calculate_meeting_time(person, start_time, duration):
    end_time = (start_time + duration) % 24
    if end_time < start_time:
        end_time += 24
    return f"{int(start_time):02d}:{int((start_time % 1) * 60):02d}", f"{int(end_time):02d}:{int((end_time % 1) * 60):02d}"

def plan_meeting(person, location, start_time, duration, travel_times, current_location, current_time):
    travel_time = calculate_travel_time(current_location, location, travel_times)
    meeting_start_time, meeting_end_time = calculate_meeting_time(person, current_time + travel_time, duration / 60)
    return {
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": meeting_start_time,
        "end_time": meeting_end_time
    }

def main():
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Nob Hill"): 7,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Nob Hill"): 8,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Nob Hill"): 9,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Nob Hill"): 12,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Golden Gate Park"): 17
    }

    meetings = [
        {"person": "Sandra", "location": "Nob Hill", "start_time": 8, "end_time": 15.5, "duration": 15},
        {"person": "Jeffrey", "location": "Union Square", "start_time": 9.5, "end_time": 15.5, "duration": 120},
        {"person": "Robert", "location": "Chinatown", "start_time": 12.25, "end_time": 16.75, "duration": 90},
        {"person": "Mark", "location": "Golden Gate Park", "start_time": 11.5, "end_time": 17.75, "duration": 15},
        {"person": "Carol", "location": "Mission District", "start_time": 18.25, "end_time": 21.25, "duration": 15},
        {"person": "James", "location": "Pacific Heights", "start_time": 20, "end_time": 22, "duration": 120}
    ]

    itinerary = []
    current_location = "North Beach"
    current_time = 9

    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start_time"])

    for meeting in meetings:
        travel_time = calculate_travel_time(current_location, meeting["location"], travel_times)
        if current_time + travel_time < meeting["start_time"]:
            current_time = meeting["start_time"] - travel_time
        itinerary.append(plan_meeting(meeting["person"], meeting["location"], current_time + travel_time, meeting["duration"], travel_times, current_location, current_time))
        current_location = meeting["location"]
        current_time += travel_time + meeting["duration"] / 60

    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()