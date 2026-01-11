import json

# Define travel times
travel_times = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
}

# Define meeting constraints
meetings = {
    "Stephanie": {"location": "Golden Gate Park", "start": 11 * 60, "end": 15 * 60, "duration": 105},
    "Karen": {"location": "Chinatown", "start": 1 * 45 + 12 * 60, "end": 4 * 60 + 30, "duration": 15},
    "Brian": {"location": "Union Square", "start": 3 * 60, "end": 5 * 60 + 15, "duration": 30},
    "Rebecca": {"location": "Fisherman's Wharf", "start": 8 * 60, "end": 11 * 60 + 15, "duration": 30},
    "Joseph": {"location": "Pacific Heights", "start": 8 * 60 + 15, "end": 9 * 60 + 30, "duration": 60},
    "Steven": {"location": "North Beach", "start": 2 * 30 + 12 * 60, "end": 8 * 45 + 12 * 60, "duration": 120},
}

# Convert time to minutes since midnight
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Convert minutes since midnight to time string
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes}"

# Main function to generate the itinerary
def generate_itinerary():
    current_time = 9 * 60  # Start at 9:00 AM
    current_location = "Financial District"
    itinerary = []

    def can_meet(meeting, current_time, current_location):
        location = meeting["location"]
        start_time = meeting["start"]
        end_time = meeting["end"]
        duration = meeting["duration"]
        
        # Calculate travel time
        travel_time = travel_times.get((current_location, location), float('inf'))
        
        # Check if we can reach the location in time
        arrival_time = current_time + travel_time
        if arrival_time + duration > end_time:
            return False
        
        # Check if the meeting starts after the person is available
        if arrival_time < start_time:
            arrival_time = start_time
        
        # Check if the meeting fits within the person's availability
        if arrival_time + duration <= end_time:
            return True
        return False

    # Sort meetings by start time to prioritize earlier meetings
    sorted_meetings = sorted(meetings.values(), key=lambda x: x["start"])

    for meeting in sorted_meetings:
        if can_meet(meeting, current_time, current_location):
            location = meeting["location"]
            start_time = max(current_time + travel_times[(current_location, location)], meeting["start"])
            end_time = start_time + meeting["duration"]
            
            # Add the meeting to the itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": [k for k, v in meetings.items() if v == meeting][0],
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
            
            # Update current time and location
            current_time = end_time
            current_location = location

    return itinerary

# Generate and print the itinerary
itinerary = generate_itinerary()
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))