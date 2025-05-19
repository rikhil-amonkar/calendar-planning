import json

def calculate_travel_time(origin, destination, travel_times):
    return travel_times.get((origin, destination), 0)

def calculate_meeting_time(person, start_time, duration):
    end_time = (start_time + duration) % 24
    if end_time < start_time:
        end_time += 24
    return f"{start_time}:{00:02d}" if start_time < 10 else f"{start_time}:00", f"{end_time}:{00:02d}" if end_time < 10 else f"{end_time}:00"

def plan_meeting(person, location, start_time, duration, travel_times, current_location, current_time):
    travel_time = calculate_travel_time(current_location, location, travel_times)
    meeting_start_time, meeting_end_time = calculate_meeting_time(person, current_time + travel_time, duration)
    return {
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": meeting_start_time,
        "end_time": meeting_end_time
    }

def main():
    travel_times = {
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Sunset District"): 17,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Sunset District"): 19,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Sunset District"): 15,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Sunset District"): 27,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Sunset District"): 30,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Sunset District"): 11,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Sunset District"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30
    }

    meetings = [
        {"person": "Elizabeth", "location": "Marina District", "start_time": 19, "end_time": 20.75, "duration": 105},
        {"person": "Joshua", "location": "Presidio", "start_time": 8.5, "end_time": 13.25, "duration": 105},
        {"person": "Timothy", "location": "North Beach", "start_time": 19.75, "end_time": 22, "duration": 90},
        {"person": "David", "location": "Embarcadero", "start_time": 10.75, "end_time": 12.5, "duration": 30},
        {"person": "Kimberly", "location": "Haight-Ashbury", "start_time": 16.75, "end_time": 21.5, "duration": 75},
        {"person": "Lisa", "location": "Golden Gate Park", "start_time": 17.5, "end_time": 21.75, "duration": 45},
        {"person": "Ronald", "location": "Richmond District", "start_time": 8, "end_time": 9.5, "duration": 90},
        {"person": "Stephanie", "location": "Alamo Square", "start_time": 15.5, "end_time": 16.5, "duration": 30},
        {"person": "Helen", "location": "Financial District", "start_time": 17.5, "end_time": 18.5, "duration": 45},
        {"person": "Laura", "location": "Sunset District", "start_time": 17.75, "end_time": 21.25, "duration": 90}
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