import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    "Russian Hill": {
        "Presidio": 14,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "Richmond District": 14,
        "Fisherman's Wharf": 7,
        "Golden Gate Park": 21,
        "Bayview": 23
    },
    "Presidio": {
        "Russian Hill": 14,
        "Chinatown": 21,
        "Pacific Heights": 11,
        "Richmond District": 7,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Bayview": 31
    },
    "Chinatown": {
        "Russian Hill": 7,
        "Presidio": 19,
        "Pacific Heights": 10,
        "Richmond District": 20,
        "Fisherman's Wharf": 8,
        "Golden Gate Park": 23,
        "Bayview": 22
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "Presidio": 11,
        "Chinatown": 11,
        "Richmond District": 12,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15,
        "Bayview": 22
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Presidio": 7,
        "Chinatown": 20,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Bayview": 26
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Presidio": 17,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "Richmond District": 18,
        "Golden Gate Park": 25,
        "Bayview": 26
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Presidio": 11,
        "Chinatown": 23,
        "Pacific Heights": 16,
        "Richmond District": 7,
        "Fisherman's Wharf": 24,
        "Bayview": 23
    },
    "Bayview": {
        "Russian Hill": 23,
        "Presidio": 31,
        "Chinatown": 18,
        "Pacific Heights": 23,
        "Richmond District": 25,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22
    }
}

# Friend constraints
friends = [
    {
        "name": "Matthew",
        "location": "Presidio",
        "available_start": "11:00",
        "available_end": "21:00",
        "min_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "available_start": "9:15",
        "available_end": "18:45",
        "min_duration": 90
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "available_start": "14:15",
        "available_end": "17:00",
        "min_duration": 15
    },
    {
        "name": "Helen",
        "location": "Richmond District",
        "available_start": "19:45",
        "available_end": "22:00",
        "min_duration": 60
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "available_start": "21:15",
        "available_end": "22:15",
        "min_duration": 60
    },
    {
        "name": "Kimberly",
        "location": "Golden Gate Park",
        "available_start": "13:00",
        "available_end": "16:30",
        "min_duration": 120
    },
    {
        "name": "Kenneth",
        "location": "Bayview",
        "available_start": "14:30",
        "available_end": "18:00",
        "min_duration": 60
    }
]

def generate_schedules():
    # Generate all possible orders of meeting friends
    friend_indices = list(range(len(friends)))
    # We'll limit permutations to 5 friends to keep computation reasonable
    for perm in permutations(friend_indices, min(5, len(friends))):
        yield [friends[i] for i in perm]

def is_schedule_valid(schedule, current_time, current_location):
    itinerary = []
    for friend in schedule:
        # Calculate travel time
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        
        # Check if we can arrive during friend's availability
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        
        # Determine meeting start time (max of arrival and friend's start time)
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend["min_duration"]
        
        # Check if meeting fits within friend's availability
        if meeting_end > available_end:
            return None  # Invalid schedule
        
        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend["location"]
    
    return itinerary

def find_optimal_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Start at Russian Hill at 9:00 (540 minutes)
    current_time = time_to_minutes("9:00")
    current_location = "Russian Hill"
    
    for schedule in generate_schedules():
        itinerary = is_schedule_valid(schedule, current_time, current_location)
        if itinerary and len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_schedule = itinerary
    
    return best_schedule

def main():
    optimal_schedule = find_optimal_schedule()
    result = {
        "itinerary": optimal_schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()