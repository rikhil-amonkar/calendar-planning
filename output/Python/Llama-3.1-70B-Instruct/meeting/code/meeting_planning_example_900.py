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
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Bayview"): 27,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Bayview"): 19,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Bayview"): 27,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Bayview"): 22,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Bayview"): 14,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Mission District"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 20,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Bayview"): 23,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Bayview"): 16,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16
    }

    meetings = [
        {"person": "Elizabeth", "location": "Alamo Square", "start_time": 13, "end_time": 17.25, "duration": 120},
        {"person": "Emily", "location": "Pacific Heights", "start_time": 11.25, "end_time": 19.75, "duration": 15},
        {"person": "Karen", "location": "Haight-Ashbury", "start_time": 11.75, "end_time": 17.5, "duration": 30},
        {"person": "Stephanie", "location": "Mission District", "start_time": 13, "end_time": 15.75, "duration": 75},
        {"person": "Brian", "location": "Marina District", "start_time": 14.25, "end_time": 22, "duration": 30},
        {"person": "Rebecca", "location": "Nob Hill", "start_time": 15.25, "end_time": 19.25, "duration": 105},
        {"person": "James", "location": "Chinatown", "start_time": 14.5, "end_time": 19, "duration": 120},
        {"person": "Steven", "location": "Russian Hill", "start_time": 14, "end_time": 20, "duration": 30},
        {"person": "Matthew", "location": "The Castro", "start_time": 16.5, "end_time": 20, "duration": 45},
        {"person": "William", "location": "Bayview", "start_time": 18.25, "end_time": 20.25, "duration": 90}
    ]

    itinerary = []
    current_location = "Richmond District"
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