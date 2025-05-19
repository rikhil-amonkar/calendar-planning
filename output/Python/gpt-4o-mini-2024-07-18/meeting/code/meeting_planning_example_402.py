import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
}

# Meeting constraints
meeting_constraints = {
    "Sarah": {"location": "Haight-Ashbury", "start": "17:00", "end": "21:30", "duration": 105},
    "Patricia": {"location": "Sunset District", "start": "17:00", "end": "19:45", "duration": 45},
    "Matthew": {"location": "Marina District", "start": "09:15", "end": "12:00", "duration": 15},
    "Joseph": {"location": "Financial District", "start": "14:15", "end": "18:45", "duration": 30},
    "Robert": {"location": "Union Square", "start": "10:15", "end": "21:45", "duration": 15},
}

# Convert time strings to datetime objects
def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Calculate the optimal meeting schedule
def calculate_schedule():
    itinerary = []
    current_time = parse_time("09:00")  # Start time at Golden Gate Park

    # Meet Matthew first
    matthew_start = max(current_time, parse_time(meeting_constraints["Matthew"]["start"]))
    matthew_end = matthew_start + timedelta(minutes=15)
    itinerary.append({
        "action": "meet",
        "location": "Marina District",
        "person": "Matthew",
        "start_time": matthew_start.strftime("%H:%M"),
        "end_time": matthew_end.strftime("%H:%M"),
    })
    current_time = matthew_end + timedelta(minutes=travel_times[("Marina District", "Union Square")])

    # Meet Robert next
    robert_start = max(current_time, parse_time(meeting_constraints["Robert"]["start"]))
    robert_end = robert_start + timedelta(minutes=15)
    itinerary.append({
        "action": "meet",
        "location": "Union Square",
        "person": "Robert",
        "start_time": robert_start.strftime("%H:%M"),
        "end_time": robert_end.strftime("%H:%M"),
    })
    current_time = robert_end + timedelta(minutes=travel_times[("Union Square", "Financial District")])

    # Meet Joseph next
    joseph_start = max(current_time, parse_time(meeting_constraints["Joseph"]["start"]))
    joseph_end = joseph_start + timedelta(minutes=30)
    itinerary.append({
        "action": "meet",
        "location": "Financial District",
        "person": "Joseph",
        "start_time": joseph_start.strftime("%H:%M"),
        "end_time": joseph_end.strftime("%H:%M"),
    })
    current_time = joseph_end + timedelta(minutes=travel_times[("Financial District", "Sunset District")])

    # Meet Patricia
    patricia_start = max(current_time, parse_time(meeting_constraints["Patricia"]["start"]))
    patricia_end = patricia_start + timedelta(minutes=45)
    itinerary.append({
        "action": "meet",
        "location": "Sunset District",
        "person": "Patricia",
        "start_time": patricia_start.strftime("%H:%M"),
        "end_time": patricia_end.strftime("%H:%M"),
    })
    current_time = patricia_end + timedelta(minutes=travel_times[("Sunset District", "Haight-Ashbury")])

    # Meet Sarah last
    sarah_start = max(current_time, parse_time(meeting_constraints["Sarah"]["start"]))
    sarah_end = sarah_start + timedelta(minutes=105)
    itinerary.append({
        "action": "meet",
        "location": "Haight-Ashbury",
        "person": "Sarah",
        "start_time": sarah_start.strftime("%H:%M"),
        "end_time": sarah_end.strftime("%H:%M"),
    })

    return {"itinerary": itinerary}

# Main function to output the itinerary
def main():
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()