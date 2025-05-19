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
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Mission District"): 26,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Mission District"): 13,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Mission District"): 18,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Mission District"): 18,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "North Beach"): 17
    }

    meetings = [
        {"person": "Jessica", "location": "Golden Gate Park", "start_time": 13.75, "end_time": 15, "duration": 30},
        {"person": "Ashley", "location": "Bayview", "start_time": 17.25, "end_time": 20, "duration": 105},
        {"person": "Ronald", "location": "Chinatown", "start_time": 7.25, "end_time": 14.75, "duration": 90},
        {"person": "William", "location": "North Beach", "start_time": 13.25, "end_time": 20.25, "duration": 15},
        {"person": "Daniel", "location": "Mission District", "start_time": 7, "end_time": 11.25, "duration": 105}
    ]

    itinerary = []
    current_location = "Presidio"
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