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
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Financial District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Financial District"): 17,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Mission District"): 17
    }

    meetings = [
        {"person": "Laura", "location": "Mission District", "start_time": 12.25, "end_time": 19.75, "duration": 75},
        {"person": "Anthony", "location": "Financial District", "start_time": 12.5, "end_time": 14.75, "duration": 30}
    ]

    itinerary = []
    current_location = "The Castro"
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