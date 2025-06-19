import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_distances = {
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Financial District": 5,
        "Russian Hill": 8,
        "Marina District": 12,
        "Richmond District": 21,
        "Pacific Heights": 11,
        "Haight-Ashbury": 21,
        "Presidio": 20,
        "Nob Hill": 10,
        "The Castro": 25
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Financial District": 11,
        "Russian Hill": 7,
        "Marina District": 9,
        "Richmond District": 18,
        "Pacific Heights": 12,
        "Haight-Ashbury": 22,
        "Presidio": 17,
        "Nob Hill": 11,
        "The Castro": 27
    },
    "Financial District": {
        "Embarcadero": 4,
        "Fisherman's Wharf": 10,
        "Russian Hill": 11,
        "Marina District": 15,
        "Richmond District": 21,
        "Pacific Heights": 13,
        "Haight-Ashbury": 19,
        "Presidio": 22,
        "Nob Hill": 8,
        "The Castro": 20
    },
    "Russian Hill": {
        "Embarcadero": 8,
        "Fisherman's Wharf": 7,
        "Financial District": 11,
        "Marina District": 7,
        "Richmond District": 14,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Presidio": 14,
        "Nob Hill": 5,
        "The Castro": 21
    },
    "Marina District": {
        "Embarcadero": 14,
        "Fisherman's Wharf": 10,
        "Financial District": 17,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Pacific Heights": 7,
        "Haight-Ashbury": 16,
        "Presidio": 10,
        "Nob Hill": 12,
        "The Castro": 22
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Fisherman's Wharf": 18,
        "Financial District": 22,
        "Russian Hill": 13,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Haight-Ashbury": 10,
        "Presidio": 7,
        "Nob Hill": 17,
        "The Castro": 16
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Fisherman's Wharf": 13,
        "Financial District": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "Richmond District": 12,
        "Haight-Ashbury": 11,
        "Presidio": 11,
        "Nob Hill": 8,
        "The Castro": 16
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Financial District": 21,
        "Russian Hill": 17,
        "Marina District": 17,
        "Richmond District": 10,
        "Pacific Heights": 12,
        "Presidio": 15,
        "Nob Hill": 15,
        "The Castro": 6
    },
    "Presidio": {
        "Embarcadero": 20,
        "Fisherman's Wharf": 19,
        "Financial District": 23,
        "Russian Hill": 14,
        "Marina District": 11,
        "Richmond District": 7,
        "Pacific Heights": 11,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "The Castro": 21
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Fisherman's Wharf": 10,
        "Financial District": 9,
        "Russian Hill": 5,
        "Marina District": 11,
        "Richmond District": 14,
        "Pacific Heights": 8,
        "Haight-Ashbury": 13,
        "Presidio": 17,
        "The Castro": 17
    },
    "The Castro": {
        "Embarcadero": 22,
        "Fisherman's Wharf": 24,
        "Financial District": 21,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Pacific Heights": 16,
        "Haight-Ashbury": 6,
        "Presidio": 20,
        "Nob Hill": 16
    }
}

# Meeting constraints
meeting_constraints = {
    "Stephanie": {"start_time": "15:30", "end_time": "22:00", "duration": 30},
    "Lisa": {"start_time": "10:45", "end_time": "17:15", "duration": 15},
    "Melissa": {"start_time": "17:00", "end_time": "21:45", "duration": 120},
    "Betty": {"start_time": "10:45", "end_time": "14:15", "duration": 60},
    "Sarah": {"start_time": "16:15", "end_time": "19:30", "duration": 105},
    "Daniel": {"start_time": "18:30", "end_time": "21:45", "duration": 60},
    "Joshua": {"start_time": "09:00", "end_time": "14:30", "duration": 15},
    "Joseph": {"start_time": "07:00", "end_time": "13:00", "duration": 45},
    "Andrew": {"start_time": "19:45", "end_time": "22:00", "duration": 105},
    "John": {"start_time": "13:15", "end_time": "19:45", "duration": 45}
}

def calculate_meeting_schedule():
    # Start at Embarcadero at 9:00 AM
    current_location = "Embarcadero"
    current_time = datetime.strptime("09:00", "%H:%M")
    schedule = []

    while True:
        # Find all people whose constraints are met at the current time
        people_to_meet = {}
        for person, constraint in meeting_constraints.items():
            start_time = datetime.strptime(constraint["start_time"], "%H:%M")
            end_time = datetime.strptime(constraint["end_time"], "%H:%M")
            if start_time <= current_time <= end_time:
                people_to_meet[person] = constraint

        # If no people's constraints are met, break the loop
        if not people_to_meet:
            break

        # Find the person who can be met the earliest
        earliest_person = min(people_to_meet, key=lambda person: meeting_constraints[person]["start_time"])
        constraint = people_to_meet[earliest_person]

        # Add the meeting to the schedule
        schedule.append({"action": "meet", "location": current_location, "person": earliest_person, "start_time": current_time.strftime("%H:%M"), "end_time": (current_time + timedelta(minutes=constraint["duration"])).strftime("%H:%M")})

        # Update the current time and location
        current_time += timedelta(minutes=constraint["duration"])
        travel_time = travel_distances[current_location][current_location]
        current_time += timedelta(minutes=travel_time)

        # Update the current location
        current_location = min(travel_distances[current_location], key=lambda location: travel_distances[current_location][location])

    return schedule

def main():
    schedule = calculate_meeting_schedule()
    output = {"itinerary": schedule}
    print(json.dumps(output, indent=4))

if __name__ == "__main__":
    main()