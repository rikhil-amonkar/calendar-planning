import json
from datetime import datetime, timedelta

# Meeting locations and travel times (in minutes)
travel_times = {
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Presidio"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Presidio"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
}

# Meeting constraints
constraints = {
    "Stephanie": {"location": "Richmond District", "start": "16:15", "end": "21:30", "duration": 75},
    "William": {"location": "Union Square", "start": "10:45", "end": "17:30", "duration": 45},
    "Elizabeth": {"location": "Nob Hill", "start": "12:15", "end": "15:00", "duration": 105},
    "Joseph": {"location": "Fisherman's Wharf", "start": "12:45", "end": "14:00", "duration": 75},
    "Anthony": {"location": "Golden Gate Park", "start": "13:00", "end": "20:30", "duration": 75},
    "Barbara": {"location": "Embarcadero", "start": "19:15", "end": "20:30", "duration": 75},
    "Carol": {"location": "Financial District", "start": "11:45", "end": "16:15", "duration": 60},
    "Sandra": {"location": "North Beach", "start": "10:00", "end": "12:30", "duration": 15},
    "Kenneth": {"location": "Presidio", "start": "21:15", "end": "22:15", "duration": 45},
}

# Convert time strings to datetime objects
def time_to_dt(t):
    return datetime.strptime(t, '%H:%M')

# Function to calculate meeting schedules
def calculate_meetings(travel_times, constraints):
    itinerary = []
    current_time = time_to_dt("9:00")

    for name, info in constraints.items():
        location = info['location']
        start_time = time_to_dt(info['start'])
        end_time = time_to_dt(info['end'])
        duration = info['duration']

        # Check if we can schedule the meeting
        travel_time = travel_times.get((current_time.strftime('%I:%M %p'), location), None)
        if travel_time is not None:
            arrival = current_time + timedelta(minutes=travel_time)
            # Adjust arrival time within the availability of the person
            if arrival < start_time:
                arrival = start_time
            departure = arrival + timedelta(minutes=duration)

            if departure <= end_time:
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": name,
                    "start_time": arrival.strftime("%H:%M"),
                    "end_time": departure.strftime("%H:%M"),
                })
                # Update current time after meeting
                current_time = departure + timedelta(minutes=travel_times.get((location, 'Marina District'), 0))

    return {"itinerary": itinerary}

# Calculate meeting schedules
optimal_schedule = calculate_meetings(travel_times, constraints)

# Output the result in JSON format
print(json.dumps(optimal_schedule, indent=2))