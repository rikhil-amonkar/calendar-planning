import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
locations = [
    "Golden Gate Park", "Haight-Ashbury", "Fisherman's Wharf", "The Castro",
    "Chinatown", "Alamo Square", "North Beach", "Russian Hill"
]

# Travel times matrix (minutes)
travel_times = {
    "Golden Gate Park": {
        "Golden Gate Park": 0,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Chinatown": 23,
        "Alamo Square": 10,
        "North Beach": 24,
        "Russian Hill": 19
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Haight-Ashbury": 0,
        "Fisherman's Wharf": 23,
        "The Castro": 6,
        "Chinatown": 19,
        "Alamo Square": 5,
        "North Beach": 19,
        "Russian Hill": 17
    },
    "Fisherman's Wharf": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 22,
        "Fisherman's Wharf": 0,
        "The Castro": 26,
        "Chinatown": 12,
        "Alamo Square": 20,
        "North Beach": 6,
        "Russian Hill": 7
    },
    "The Castro": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 6,
        "Fisherman's Wharf": 24,
        "The Castro": 0,
        "Chinatown": 20,
        "Alamo Square": 8,
        "North Beach": 20,
        "Russian Hill": 18
    },
    "Chinatown": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        "Chinatown": 0,
        "Alamo Square": 17,
        "North Beach": 3,
        "Russian Hill": 7
    },
    "Alamo Square": {
        "Golden Gate Park": 9,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Chinatown": 16,
        "Alamo Square": 0,
        "North Beach": 15,
        "Russian Hill": 13
    },
    "North Beach": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Chinatown": 6,
        "Alamo Square": 16,
        "North Beach": 0,
        "Russian Hill": 4
    },
    "Russian Hill": {
        "Golden Gate Park": 21,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Chinatown": 9,
        "Alamo Square": 15,
        "North Beach": 5,
        "Russian Hill": 0
    }
}

friends = [
    {
        "name": "Carol",
        "location": "Haight-Ashbury",
        "available_start": "21:30",
        "available_end": "22:30",
        "duration": 60
    },
    {
        "name": "Laura",
        "location": "Fisherman's Wharf",
        "available_start": "11:45",
        "available_end": "21:30",
        "duration": 60
    },
    {
        "name": "Karen",
        "location": "The Castro",
        "available_start": "7:15",
        "available_end": "14:00",
        "duration": 75
    },
    {
        "name": "Elizabeth",
        "location": "Chinatown",
        "available_start": "12:15",
        "available_end": "21:30",
        "duration": 75
    },
    {
        "name": "Deborah",
        "location": "Alamo Square",
        "available_start": "12:00",
        "available_end": "15:00",
        "duration": 105
    },
    {
        "name": "Jason",
        "location": "North Beach",
        "available_start": "14:45",
        "available_end": "19:00",
        "duration": 90
    },
    {
        "name": "Steven",
        "location": "Russian Hill",
        "available_start": "14:45",
        "available_end": "18:30",
        "duration": 120
    }
]

def get_available_time_slots(friend, current_time):
    start = max(time_to_minutes(friend["available_start"]), current_time)
    end = time_to_minutes(friend["available_end"])
    duration = friend["duration"]
    
    if start + duration > end:
        return None
    
    return (start, start + duration)

def calculate_schedule(start_location, start_time, friends_list):
    best_schedule = []
    max_meetings = 0
    
    # Try all possible orders of meeting friends
    for order in permutations(friends_list):
        current_location = start_location
        current_time = time_to_minutes(start_time)
        schedule = []
        meetings = 0
        
        for friend in order:
            travel_time = travel_times[current_location][friend["location"]]
            arrival_time = current_time + travel_time
            
            time_slot = get_available_time_slots(friend, arrival_time)
            if time_slot:
                start, end = time_slot
                schedule.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
                current_time = end
                current_location = friend["location"]
                meetings += 1
        
        if meetings > max_meetings or (meetings == max_meetings and len(schedule) > len(best_schedule)):
            max_meetings = meetings
            best_schedule = schedule
    
    return best_schedule

# Calculate optimal schedule
start_location = "Golden Gate Park"
start_time = "9:00"
optimal_schedule = calculate_schedule(start_location, start_time, friends)

# Prepare output
output = {
    "itinerary": optimal_schedule
}

# Print JSON output
print(json.dumps(output, indent=2))