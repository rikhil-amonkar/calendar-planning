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
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "The Castro"): 20,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Russian Hill"): 23,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Nob Hill"): 8,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Russian Hill"): 14,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Pacific Heights"): 7
    }

    meetings = [
        {"person": "Nancy", "location": "Presidio", "start_time": 11.75, "end_time": 22, "duration": 30},
        {"person": "Matthew", "location": "Russian Hill", "start_time": 15.75, "end_time": 21.75, "duration": 75},
        {"person": "Karen", "location": "The Castro", "start_time": 17, "end_time": 19, "duration": 45},
        {"person": "Paul", "location": "Nob Hill", "start_time": 16.25, "end_time": 21.25, "duration": 60},
        {"person": "Jeffrey", "location": "Pacific Heights", "start_time": 20, "end_time": 20.75, "duration": 45},
        {"person": "Patricia", "location": "Chinatown", "start_time": 20, "end_time": 21.75, "duration": 75},
        {"person": "Carol", "location": "Union Square", "start_time": 18, "end_time": 20.25, "duration": 120}
    ]

    itinerary = []
    current_location = "Bayview"
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