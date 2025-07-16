import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Presidio': {
        'Fisherman\'s Wharf': 19,
        'Alamo Square': 19,
        'Financial District': 23,
        'Union Square': 22,
        'Sunset District': 15,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Alamo Square': 21,
        'Financial District': 11,
        'Union Square': 13,
        'Sunset District': 27,
        'Embarcadero': 8,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Richmond District': 18
    },
    'Alamo Square': {
        'Presidio': 17,
        'Fisherman\'s Wharf': 19,
        'Financial District': 17,
        'Union Square': 14,
        'Sunset District': 16,
        'Embarcadero': 16,
        'Golden Gate Park': 9,
        'Chinatown': 15,
        'Richmond District': 11
    },
    'Financial District': {
        'Presidio': 22,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 17,
        'Union Square': 9,
        'Sunset District': 30,
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Richmond District': 21
    },
    'Union Square': {
        'Presidio': 24,
        'Fisherman\'s Wharf': 15,
        'Alamo Square': 15,
        'Financial District': 9,
        'Sunset District': 27,
        'Embarcadero': 11,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Richmond District': 20
    },
    'Sunset District': {
        'Presidio': 16,
        'Fisherman\'s Wharf': 29,
        'Alamo Square': 17,
        'Financial District': 30,
        'Union Square': 30,
        'Embarcadero': 30,
        'Golden Gate Park': 11,
        'Chinatown': 30,
        'Richmond District': 12
    },
    'Embarcadero': {
        'Presidio': 20,
        'Fisherman\'s Wharf': 6,
        'Alamo Square': 19,
        'Financial District': 5,
        'Union Square': 10,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Chinatown': 7,
        'Richmond District': 21
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Fisherman\'s Wharf': 24,
        'Alamo Square': 9,
        'Financial District': 26,
        'Union Square': 22,
        'Sunset District': 10,
        'Embarcadero': 25,
        'Chinatown': 23,
        'Richmond District': 7
    },
    'Chinatown': {
        'Presidio': 19,
        'Fisherman\'s Wharf': 8,
        'Alamo Square': 17,
        'Financial District': 5,
        'Union Square': 7,
        'Sunset District': 29,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
        'Richmond District': 20
    },
    'Richmond District': {
        'Presidio': 7,
        'Fisherman\'s Wharf': 18,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Sunset District': 11,
        'Embarcadero': 19,
        'Golden Gate Park': 9,
        'Chinatown': 20
    }
}

# Friends data: name -> (location, start, end, min_duration)
friends = {
    'Jeffrey': ('Fisherman\'s Wharf', '10:15', '13:00', 90),
    'Ronald': ('Alamo Square', '7:45', '14:45', 120),
    'Jason': ('Financial District', '10:45', '16:00', 105),
    'Melissa': ('Union Square', '17:45', '18:15', 15),
    'Elizabeth': ('Sunset District', '14:45', '17:30', 105),
    'Margaret': ('Embarcadero', '13:15', '19:00', 90),
    'George': ('Golden Gate Park', '19:00', '22:00', 75),
    'Richard': ('Chinatown', '9:30', '21:00', 15),
    'Laura': ('Richmond District', '9:45', '18:00', 60)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_available_slots(person, current_time):
    name, (loc, start, end, dur) = person
    start_min = time_to_minutes(start)
    end_min = time_to_minutes(end)
    
    if current_time >= end_min:
        return None
    
    available_start = max(start_min, current_time)
    available_end = end_min
    
    if available_end - available_start < dur:
        return None
    
    return (loc, available_start, available_end, dur)

def calculate_best_schedule():
    current_location = 'Presidio'
    current_time = time_to_minutes('9:00')
    remaining_friends = list(friends.items())
    itinerary = []
    
    # We'll try to meet friends in order of earliest availability first
    while remaining_friends:
        best_friend = None
        best_slot = None
        best_travel_time = float('inf')
        best_end_time = float('inf')
        
        for i, (name, data) in enumerate(remaining_friends):
            slot = get_available_slots((name, data), current_time + travel_times[current_location][data[0]])
            if not slot:
                continue
            
            loc, start, end, dur = slot
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time
            
            # Can't arrive before friend's start time
            if arrival_time < time_to_minutes(data[1]):
                arrival_time = time_to_minutes(data[1])
            
            # Can't stay longer than friend's availability
            actual_duration = min(dur, end - arrival_time)
            if actual_duration < data[3]:
                continue
            
            end_time = arrival_time + actual_duration
            
            # Prefer friends we can meet sooner
            if arrival_time < best_end_time:
                best_friend = (i, name)
                best_slot = (loc, arrival_time, end_time, actual_duration)
                best_travel_time = travel_time
                best_end_time = end_time
        
        if not best_friend:
            break
        
        i, name = best_friend
        loc, start, end, dur = best_slot
        
        # Add travel if needed
        if current_location != loc:
            travel_duration = travel_times[current_location][loc]
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": loc,
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_duration)
            })
            current_time += travel_duration
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        
        current_location = loc
        current_time = end
        del remaining_friends[i]
    
    return itinerary

def main():
    itinerary = calculate_best_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()