import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Presidio"): 17,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Alamo Square"): 19,
}

# Define constraints
constraints = {
    "David": {"location": "Sunset District", "start": "9:15", "end": "22:00", "min_duration": 15},
    "Kenneth": {"location": "Union Square", "start": "21:15", "end": "21:45", "min_duration": 15},
    "Patricia": {"location": "Nob Hill", "start": "15:00", "end": "19:15", "min_duration": 120},
    "Mary": {"location": "Marina District", "start": "14:45", "end": "16:45", "min_duration": 45},
    "Charles": {"location": "Richmond District", "start": "17:15", "end": "21:00", "min_duration": 15},
    "Joshua": {"location": "Financial District", "start": "14:30", "end": "17:15", "min_duration": 90},
    "Ronald": {"location": "Embarcadero", "start": "18:15", "end": "20:45", "min_duration": 30},
    "George": {"location": "The Castro", "start": "14:15", "end": "19:00", "min_duration": 105},
    "Kimberly": {"location": "Alamo Square", "start": "9:00", "end": "14:30", "min_duration": 105},
    "William": {"location": "Presidio", "start": "7:00", "end": "12:45", "min_duration": 60},
}

# Helper function to convert time string to datetime object
def time_to_datetime(time_str, base_date):
    return datetime.strptime(f"{base_date} {time_str}", "%Y-%m-%d %H:%M")

# Helper function to convert datetime object to time string
def datetime_to_time(dt):
    return dt.strftime("%H:%M")

# Main function to find the optimal schedule
def find_optimal_schedule():
    base_date = "2023-10-01"
    current_time = time_to_datetime("9:00", base_date)
    current_location = "Russian Hill"
    itinerary = []

    # Sort constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: time_to_datetime(x[1]["start"], base_date))

    for name, constraint in sorted_constraints:
        location = constraint["location"]
        start_time = time_to_datetime(constraint["start"], base_date)
        end_time = time_to_datetime(constraint["end"], base_date)
        min_duration = constraint["min_duration"]

        # Calculate travel time to the next location
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet the person within their availability
        if arrival_time + timedelta(minutes=min_duration) <= end_time:
            # Adjust meeting start time if necessary
            meeting_start_time = max(arrival_time, start_time)
            meeting_end_time = meeting_start_time + timedelta(minutes=min_duration)

            # Add to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": datetime_to_time(meeting_start_time),
                "end_time": datetime_to_time(meeting_end_time)
            })

            # Update current time and location
            current_time = meeting_end_time
            current_location = location

    return itinerary

# Generate the optimal schedule
optimal_itinerary = find_optimal_schedule()

# Output the result as JSON
result = {
    "itinerary": optimal_itinerary
}
print(json.dumps(result))