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
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Pacific Heights"): 11,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13
    }

    meetings = [
        {"person": "John", "location": "Pacific Heights", "start_time": 9, "end_time": 13.5, "duration": 15},
        {"person": "Jeffrey", "location": "Presidio", "start_time": 8, "end_time": 10, "duration": 105},
        {"person": "Steven", "location": "North Beach", "start_time": 13.5, "end_time": 22, "duration": 45},
        {"person": "Barbara", "location": "Fisherman's Wharf", "start_time": 18, "end_time": 21.5, "duration": 30}
    ]

    itinerary = []
    current_location = "Nob Hill"
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