import json
from itertools import permutations

# Travel times dictionary (from_location, to_location) -> minutes
travel_times = {
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Presidio'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Presidio'): 20,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Presidio'): 22,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Presidio'): 17,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'North Beach'): 18
}

# Friend data: name -> (location, available_start, available_end, min_duration)
friends = {
    'Stephanie': ('Richmond District', '16:15', '21:30', 75),
    'William': ('Union Square', '10:45', '17:30', 45),
    'Elizabeth': ('Nob Hill', '12:15', '15:00', 105),
    'Joseph': ('Fisherman\'s Wharf', '12:45', '14:00', 75),
    'Anthony': ('Golden Gate Park', '13:00', '20:30', 75),
    'Barbara': ('Embarcadero', '19:15', '20:30', 75),
    'Carol': ('Financial District', '11:45', '16:15', 60),
    'Sandra': ('North Beach', '10:00', '12:30', 15),
    'Kenneth': ('Presidio', '21:15', '22:15', 45)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    current_location = 'Marina District'
    current_time = time_to_minutes('9:00')
    itinerary = []
    remaining_friends = set(friends.keys())
    
    # We'll try to meet friends in order of their availability end times
    sorted_friends = sorted(friends.items(), key=lambda x: time_to_minutes(x[1][1]))
    
    for name, (location, avail_start, avail_end, min_duration) in sorted_friends:
        if name not in remaining_friends:
            continue
            
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        # Can we meet this friend?
        meeting_start = max(arrival_time, avail_start_min)
        meeting_end = meeting_start + min_duration
        
        if meeting_end <= avail_end_min:
            # Add to itinerary
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = location
            current_time = meeting_end
            remaining_friends.remove(name)
    
    # Try to fit remaining friends if possible
    for name in list(remaining_friends):
        location, avail_start, avail_end, min_duration = friends[name]
        travel_time = travel_times.get((current_location, location), float('inf'))
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        meeting_start = max(arrival_time, avail_start_min)
        meeting_end = meeting_start + min_duration
        
        if meeting_end <= avail_end_min:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_location = location
            current_time = meeting_end
            remaining_friends.remove(name)
    
    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()