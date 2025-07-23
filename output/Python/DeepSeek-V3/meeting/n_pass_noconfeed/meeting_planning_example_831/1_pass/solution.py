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
    "Presidio", "Fisherman's Wharf", "Alamo Square", "Financial District",
    "Union Square", "Sunset District", "Embarcadero", "Golden Gate Park",
    "Chinatown", "Richmond District"
]

travel_times = {
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Richmond District"): 21,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Richmond District"): 20,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

people = [
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "start": "10:15", "end": "13:00", "duration": 90},
    {"name": "Ronald", "location": "Alamo Square", "start": "7:45", "end": "14:45", "duration": 120},
    {"name": "Jason", "location": "Financial District", "start": "10:45", "end": "16:00", "duration": 105},
    {"name": "Melissa", "location": "Union Square", "start": "17:45", "end": "18:15", "duration": 15},
    {"name": "Elizabeth", "location": "Sunset District", "start": "14:45", "end": "17:30", "duration": 105},
    {"name": "Margaret", "location": "Embarcadero", "start": "13:15", "end": "19:00", "duration": 90},
    {"name": "George", "location": "Golden Gate Park", "start": "19:00", "end": "22:00", "duration": 75},
    {"name": "Richard", "location": "Chinatown", "start": "9:30", "end": "21:00", "duration": 15},
    {"name": "Laura", "location": "Richmond District", "start": "9:45", "end": "18:00", "duration": 60},
]

current_location = "Presidio"
current_time = time_to_minutes("9:00")

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

def find_best_schedule():
    best_schedule = []
    best_count = 0
    
    # Try all permutations of people to find best possible schedule
    for perm in permutations(people):
        schedule = []
        loc = current_location
        time = current_time
        count = 0
        
        for person in perm:
            travel_time = get_travel_time(loc, person["location"])
            arrival_time = time + travel_time
            start_time = max(arrival_time, time_to_minutes(person["start"]))
            end_time = min(start_time + person["duration"], time_to_minutes(person["end"]))
            
            if end_time > start_time and end_time <= time_to_minutes(person["end"]):
                schedule.append({
                    "action": "meet",
                    "location": person["location"],
                    "person": person["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                loc = person["location"]
                time = end_time
                count += 1
        
        if count > best_count:
            best_count = count
            best_schedule = schedule
    
    return best_schedule

best_schedule = find_best_schedule()

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))