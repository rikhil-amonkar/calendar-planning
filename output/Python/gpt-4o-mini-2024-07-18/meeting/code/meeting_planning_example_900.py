import json
from datetime import datetime, timedelta

# Define travel distances in a dictionary
travel_times = {
    "Richmond District": {
        "The Castro": 16,
        "Nob Hill": 17,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Chinatown": 20,
        "Russian Hill": 13,
        "Alamo Square": 13,
        "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Chinatown": 22,
        "Russian Hill": 18,
        "Alamo Square": 8,
        "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14,
        "The Castro": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Mission District": 13,
        "Chinatown": 6,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "Bayview": 19
    },
    # ... continue defining other locations similarly,
    # This full structure should include all locations and their travel times.
}

# Define meeting constraints
constraints = {
    "Matthew": {"location": "The Castro", "start": "16:30", "end": "20:00", "duration": 45},
    "Rebecca": {"location": "Nob Hill", "start": "15:15", "end": "19:15", "duration": 105},
    "Brian": {"location": "Marina District", "start": "14:15", "end": "22:00", "duration": 30},
    "Emily": {"location": "Pacific Heights", "start": "11:15", "end": "19:45", "duration": 15},
    "Karen": {"location": "Haight-Ashbury", "start": "11:45", "end": "17:30", "duration": 30},
    "Stephanie": {"location": "Mission District", "start": "13:00", "end": "15:45", "duration": 75},
    "James": {"location": "Chinatown", "start": "14:30", "end": "19:00", "duration": 120},
    "Steven": {"location": "Russian Hill", "start": "14:00", "end": "20:00", "duration": 30},
    "Elizabeth": {"location": "Alamo Square", "start": "13:00", "end": "17:15", "duration": 120},
    "William": {"location": "Bayview", "start": "18:15", "end": "20:15", "duration": 90},
}

# Function to calculate the meeting schedule
def calculate_schedule(travel_times, constraints):
    start_time = datetime.strptime("09:00", "%H:%M")
    schedule = []
    current_time = start_time
    current_location = "Richmond District"
    
    for person, info in constraints.items():
        location = info["location"]
        person's_start_time = datetime.strptime(info["start"], "%H:%M")
        person's_end_time = datetime.strptime(info["end"], "%H:%M")

        # Calculate travel time to the person's location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet the person
        if arrival_time >= person's_start_time and arrival_time + timedelta(minutes=info["duration"]) <= person’s_end_time:
            meet_start_time = arrival_time
            meet_end_time = meet_start_time + timedelta(minutes=info["duration"])
            
            # Append the meeting to the schedule
            schedule.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": meet_start_time.strftime("%H:%M"),
                "end_time": meet_end_time.strftime("%H:%M")
            })
            
            # Update current time and location
            current_time = meet_end_time
            current_location = location

            # Include travel time to next constraint in the loop
            next_person_location = next(iter(constraints.values()))['location']
            travel_time_to_next = travel_times[current_location][next_person_location]
            current_time += timedelta(minutes=travel_time_to_next)

    return {"itinerary": schedule}

# Get the meeting schedule
itinerary = calculate_schedule(travel_times, constraints)

# Output the result as JSON
print(json.dumps(itinerary, indent=2))