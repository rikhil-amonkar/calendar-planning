import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data
friends = {
    "Mark": {
        "location": "Fisherman's Wharf",
        "available_start": "8:15",
        "available_end": "10:00",
        "duration": 30
    },
    "Stephanie": {
        "location": "Presidio",
        "available_start": "12:15",
        "available_end": "15:00",
        "duration": 75
    },
    "Betty": {
        "location": "Bayview",
        "available_start": "7:15",
        "available_end": "20:30",
        "duration": 15
    },
    "Lisa": {
        "location": "Haight-Ashbury",
        "available_start": "15:30",
        "available_end": "18:30",
        "duration": 45
    },
    "William": {
        "location": "Russian Hill",
        "available_start": "18:45",
        "available_end": "20:00",
        "duration": 60
    },
    "Brian": {
        "location": "The Castro",
        "available_start": "9:15",
        "available_end": "13:15",
        "duration": 30
    },
    "Joseph": {
        "location": "Marina District",
        "available_start": "10:45",
        "available_end": "15:00",
        "duration": 90
    },
    "Ashley": {
        "location": "Richmond District",
        "available_start": "9:45",
        "available_end": "11:15",
        "duration": 45
    },
    "Patricia": {
        "location": "Union Square",
        "available_start": "16:30",
        "available_end": "20:00",
        "duration": 120
    },
    "Karen": {
        "location": "Sunset District",
        "available_start": "16:30",
        "available_end": "22:00",
        "duration": 105
    }
}

travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Bayview": 19,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
        "The Castro": 20,
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Sunset District": 30
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Presidio": 17,
        "Bayview": 26,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "The Castro": 27,
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Sunset District": 27
    },
    "Presidio": {
        "Financial District": 23,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
        "The Castro": 21,
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Sunset District": 15
    },
    "Bayview": {
        "Financial District": 19,
        "Fisherman's Wharf": 25,
        "Presidio": 32,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 21,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Bayview": 18,
        "Russian Hill": 17,
        "The Castro": 6,
        "Marina District": 17,
        "Richmond District": 10,
        "Union Square": 19,
        "Sunset District": 15
    },
    "Russian Hill": {
        "Financial District": 11,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Bayview": 23,
        "Haight-Ashbury": 17,
        "The Castro": 21,
        "Marina District": 7,
        "Richmond District": 14,
        "Union Square": 10,
        "Sunset District": 23
    },
    "The Castro": {
        "Financial District": 21,
        "Fisherman's Wharf": 24,
        "Presidio": 20,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Bayview": 27,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "Union Square": 16,
        "Sunset District": 19
    },
    "Richmond District": {
        "Financial District": 22,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Bayview": 15,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
        "The Castro": 17,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 30
    }
}

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, 0)

def is_schedule_valid(schedule):
    current_time = time_to_minutes("9:00")
    current_location = "Financial District"
    
    for entry in schedule:
        person = entry["person"]
        friend_data = friends[person]
        location = friend_data["location"]
        
        # Travel time
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Check if we can meet during their available time
        available_start = time_to_minutes(friend_data["available_start"])
        available_end = time_to_minutes(friend_data["available_end"])
        duration = friend_data["duration"]
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        
        if meeting_end > available_end:
            return False
        
        current_time = meeting_end
        current_location = location
    
    return True

def calculate_schedule_score(schedule):
    total_meetings = len(schedule)
    total_duration = sum(friends[entry["person"]]["duration"] for entry in schedule)
    return (total_meetings, total_duration)

def generate_best_schedule():
    friend_names = list(friends.keys())
    best_schedule = []
    best_score = (0, 0)
    
    # We'll try permutations of different lengths to find the best possible schedule
    for r in range(1, len(friend_names) + 1):
        for perm in permutations(friend_names, r):
            schedule = []
            for person in perm:
                schedule.append({"person": person})
            
            if is_schedule_valid(schedule):
                current_score = calculate_schedule_score(schedule)
                if current_score > best_score:
                    best_score = current_score
                    best_schedule = schedule
    
    # Now build the detailed itinerary
    if not best_schedule:
        return {"itinerary": []}
    
    itinerary = []
    current_time = time_to_minutes("9:00")
    current_location = "Financial District"
    
    for entry in best_schedule:
        person = entry["person"]
        friend_data = friends[person]
        location = friend_data["location"]
        
        # Travel time
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Meeting time
        available_start = time_to_minutes(friend_data["available_start"])
        available_end = time_to_minutes(friend_data["available_end"])
        duration = friend_data["duration"]
        
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return {"itinerary": itinerary}

best_schedule = generate_best_schedule()
print(json.dumps(best_schedule, indent=2))