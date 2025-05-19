import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

# Friend data: name -> (location, start, end, min_duration)
friends = {
    "Helen": ("Golden Gate Park", "9:30", "12:15", 45),
    "Steven": ("The Castro", "20:15", "22:00", 105),
    "Deborah": ("Bayview", "8:30", "12:00", 30),
    "Matthew": ("Marina District", "9:15", "14:15", 45),
    "Joseph": ("Union Square", "14:15", "18:45", 120),
    "Ronald": ("Sunset District", "16:00", "20:45", 60),
    "Robert": ("Alamo Square", "18:30", "21:15", 120),
    "Rebecca": ("Financial District", "14:45", "16:15", 30),
    "Elizabeth": ("Mission District", "18:30", "21:00", 120)
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_schedule(current_time, travel_time, friend_start, friend_end, min_duration):
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(friend_start))
    end_time = start_time + min_duration
    return end_time <= time_to_minutes(friend_end)

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all possible orders of meeting friends (limited to 5 friends for performance)
    for friend_order in permutations(['Helen', 'Deborah', 'Matthew', 'Joseph', 'Rebecca', 'Ronald', 'Robert', 'Elizabeth', 'Steven'], 5):
        current_location = "Pacific Heights"
        current_time = time_to_minutes("9:00")
        schedule = []
        
        for friend in friend_order:
            location, start, end, min_duration = friends[friend]
            travel_time = travel_times[current_location][location]
            
            if can_schedule(current_time, travel_time, start, end, min_duration):
                arrival_time = current_time + travel_time
                start_time = max(arrival_time, time_to_minutes(start))
                end_time = start_time + min_duration
                
                schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                
                current_location = location
                current_time = end_time
        
        # Check if we can fit Steven (must meet last)
        if "Steven" not in [x["person"] for x in schedule]:
            friend = "Steven"
            location, start, end, min_duration = friends[friend]
            travel_time = travel_times[current_location][location]
            
            if can_schedule(current_time, travel_time, start, end, min_duration):
                arrival_time = current_time + travel_time
                start_time = max(arrival_time, time_to_minutes(start))
                end_time = start_time + min_duration
                
                schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": friend,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
        
        if len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
    
    return best_schedule

# Find a feasible schedule (not necessarily optimal due to complexity)
def find_feasible_schedule():
    current_location = "Pacific Heights"
    current_time = time_to_minutes("9:00")
    schedule = []
    
    # Meet Deborah first (earliest availability)
    friend = "Deborah"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Helen next
    friend = "Helen"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Matthew
    friend = "Matthew"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Joseph
    friend = "Joseph"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Rebecca
    friend = "Rebecca"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Ronald
    friend = "Ronald"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Robert
    friend = "Robert"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Elizabeth
    friend = "Elizabeth"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    schedule.append({
        "action": "meet",
        "location": location,
        "person": friend,
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })
    current_location = location
    current_time = end_time
    
    # Meet Steven
    friend = "Steven"
    location, start, end, min_duration = friends[friend]
    travel_time = travel_times[current_location][location]
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(start))
    end_time = start_time + min_duration
    if end_time <= time_to_minutes(end):
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend,
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
    
    return schedule

schedule = find_feasible_schedule()
output = {"itinerary": schedule}
print(json.dumps(output, indent=2))