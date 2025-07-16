import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (simplified as symmetric)
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
        "Financial District": 10,
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
        "Financial District": 22,
        "Fisherman's Wharf": 17,
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
        "Fisherman's Wharf": 26,
        "Presidio": 31,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 19,
        "Fisherman's Wharf": 22,
        "Presidio": 15,
        "Bayview": 19,
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
        "Financial District": 20,
        "Fisherman's Wharf": 27,
        "Presidio": 21,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 21,
        "Marina District": 22,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 15,
        "Fisherman's Wharf": 9,
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
        "Financial District": 21,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 14,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 13,
        "Presidio": 22,
        "Bayview": 18,
        "Haight-Ashbury": 19,
        "Russian Hill": 10,
        "The Castro": 19,
        "Marina District": 16,
        "Richmond District": 20,
        "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 27,
        "Presidio": 15,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 23,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 27
    }
}

# Friend data: name, location, available_start, available_end, min_duration
friends = [
    ("Mark", "Fisherman's Wharf", "8:15", "10:00", 30),
    ("Stephanie", "Presidio", "12:15", "15:00", 75),
    ("Betty", "Bayview", "7:15", "20:30", 15),
    ("Lisa", "Haight-Ashbury", "15:30", "18:30", 45),
    ("William", "Russian Hill", "18:45", "20:00", 60),
    ("Brian", "The Castro", "9:15", "13:15", 30),
    ("Joseph", "Marina District", "10:45", "15:00", 90),
    ("Ashley", "Richmond District", "9:45", "11:15", 45),
    ("Patricia", "Union Square", "16:30", "20:00", 120),
    ("Karen", "Sunset District", "16:30", "22:00", 105)
]

def get_travel_time(from_loc, to_loc):
    return travel_times[from_loc][to_loc]

def is_schedule_valid(schedule):
    current_time = time_to_minutes("9:00")
    current_location = "Financial District"
    
    for entry in schedule:
        person, location, avail_start, avail_end, min_duration = entry
        travel_time = get_travel_time(current_location, location)
        
        # Arrival time at new location
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        # Calculate meeting window
        meeting_start = max(arrival_time, avail_start_min)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > avail_end_min:
            return False
        
        current_time = meeting_end
        current_location = location
    
    return True

def calculate_total_meeting_time(schedule):
    return sum(entry[4] for entry in schedule)

def generate_best_schedule():
    best_schedule = []
    best_time = 0
    
    # Try different orders of friends (limited to feasible subsets)
    friend_subsets = [
        [friends[0], friends[5], friends[7], friends[6], friends[1], friends[3], friends[8]],  # Mark, Brian, Ashley, Joseph, Stephanie, Lisa, Patricia
        [friends[0], friends[5], friends[7], friends[6], friends[1], friends[3], friends[9]],  # Mark, Brian, Ashley, Joseph, Stephanie, Lisa, Karen
        [friends[0], friends[5], friends[7], friends[6], friends[1], friends[4], friends[8]],  # Mark, Brian, Ashley, Joseph, Stephanie, William, Patricia
        [friends[0], friends[5], friends[7], friends[6], friends[1], friends[4], friends[9]],  # Mark, Brian, Ashley, Joseph, Stephanie, William, Karen
    ]
    
    for subset in friend_subsets:
        for order in permutations(subset):
            if is_schedule_valid(order):
                total_time = calculate_total_meeting_time(order)
                if total_time > best_time:
                    best_time = total_time
                    best_schedule = order
    
    return best_schedule

def build_itinerary(schedule):
    itinerary = []
    current_time = time_to_minutes("9:00")
    current_location = "Financial District"
    
    for entry in schedule:
        person, location, avail_start, avail_end, min_duration = entry
        travel_time = get_travel_time(current_location, location)
        
        # Travel action
        if current_location != location:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": location,
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_time)
            })
            current_time += travel_time
        
        # Meeting action
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        meeting_start = max(current_time, avail_start_min)
        meeting_end = meeting_start + min_duration
        
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return itinerary

best_schedule = generate_best_schedule()
itinerary = build_itinerary(best_schedule)

output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))