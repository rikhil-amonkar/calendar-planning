import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: {from: {to: minutes}}
travel_times = {
    "Russian Hill": {
        "Pacific Heights": 7, "North Beach": 5, "Golden Gate Park": 21, "Embarcadero": 8,
        "Haight-Ashbury": 17, "Fisherman's Wharf": 7, "Mission District": 16, "Alamo Square": 15,
        "Bayview": 23, "Richmond District": 14
    },
    "Pacific Heights": {
        "Russian Hill": 7, "North Beach": 9, "Golden Gate Park": 15, "Embarcadero": 10,
        "Haight-Ashbury": 11, "Fisherman's Wharf": 13, "Mission District": 15, "Alamo Square": 10,
        "Bayview": 22, "Richmond District": 12
    },
    "North Beach": {
        "Russian Hill": 4, "Pacific Heights": 8, "Golden Gate Park": 22, "Embarcadero": 6,
        "Haight-Ashbury": 18, "Fisherman's Wharf": 5, "Mission District": 18, "Alamo Square": 16,
        "Bayview": 25, "Richmond District": 18
    },
    "Golden Gate Park": {
        "Russian Hill": 19, "Pacific Heights": 16, "North Beach": 23, "Embarcadero": 25,
        "Haight-Ashbury": 7, "Fisherman's Wharf": 24, "Mission District": 17, "Alamo Square": 9,
        "Bayview": 23, "Richmond District": 7
    },
    "Embarcadero": {
        "Russian Hill": 8, "Pacific Heights": 11, "North Beach": 5, "Golden Gate Park": 25,
        "Haight-Ashbury": 21, "Fisherman's Wharf": 6, "Mission District": 20, "Alamo Square": 19,
        "Bayview": 21, "Richmond District": 21
    },
    "Haight-Ashbury": {
        "Russian Hill": 17, "Pacific Heights": 12, "North Beach": 19, "Golden Gate Park": 7,
        "Embarcadero": 20, "Fisherman's Wharf": 23, "Mission District": 11, "Alamo Square": 5,
        "Bayview": 18, "Richmond District": 10
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7, "Pacific Heights": 12, "North Beach": 6, "Golden Gate Park": 25,
        "Embarcadero": 8, "Haight-Ashbury": 22, "Mission District": 22, "Alamo Square": 21,
        "Bayview": 26, "Richmond District": 18
    },
    "Mission District": {
        "Russian Hill": 15, "Pacific Heights": 16, "North Beach": 17, "Golden Gate Park": 17,
        "Embarcadero": 19, "Haight-Ashbury": 12, "Fisherman's Wharf": 22, "Alamo Square": 11,
        "Bayview": 14, "Richmond District": 20
    },
    "Alamo Square": {
        "Russian Hill": 13, "Pacific Heights": 10, "North Beach": 15, "Golden Gate Park": 9,
        "Embarcadero": 16, "Haight-Ashbury": 5, "Fisherman's Wharf": 19, "Mission District": 10,
        "Bayview": 16, "Richmond District": 11
    },
    "Bayview": {
        "Russian Hill": 23, "Pacific Heights": 23, "North Beach": 22, "Golden Gate Park": 22,
        "Embarcadero": 19, "Haight-Ashbury": 19, "Fisherman's Wharf": 25, "Mission District": 13,
        "Alamo Square": 16, "Richmond District": 27
    },
    "Richmond District": {
        "Russian Hill": 13, "Pacific Heights": 10, "North Beach": 17, "Golden Gate Park": 9,
        "Embarcadero": 19, "Haight-Ashbury": 10, "Fisherman's Wharf": 18, "Mission District": 20,
        "Alamo Square": 13, "Bayview": 27
    }
}

# Friend constraints: (name, location, available_start, available_end, min_duration)
friends = [
    ("Emily", "Pacific Heights", "9:15", "13:45", 120),
    ("Helen", "North Beach", "13:45", "18:45", 30),
    ("Kimberly", "Golden Gate Park", "18:45", "21:15", 75),
    ("James", "Embarcadero", "10:30", "11:30", 30),
    ("Linda", "Haight-Ashbury", "7:30", "19:15", 15),
    ("Paul", "Fisherman's Wharf", "14:45", "18:45", 90),
    ("Anthony", "Mission District", "8:00", "14:45", 105),
    ("Nancy", "Alamo Square", "8:30", "13:45", 120),
    ("William", "Bayview", "17:30", "20:30", 120),
    ("Margaret", "Richmond District", "15:15", "18:15", 45)
]

def generate_schedule():
    current_location = "Russian Hill"
    current_time = time_to_minutes("9:00")
    itinerary = []
    
    # Sort friends by urgency (earlier available_end first)
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x[3]))
    
    # First handle James since he has a very tight window
    for friend in sorted_friends:
        name, location, avail_start, avail_end, min_duration = friend
        if name == "James":
            travel_time = travel_times[current_location].get(location, 0)
            arrival_time = current_time + travel_time
            avail_start_min = time_to_minutes(avail_start)
            avail_end_min = time_to_minutes(avail_end)
            latest_start = avail_end_min - min_duration
            start_time = max(arrival_time, avail_start_min)
            
            if start_time <= latest_start:
                end_time = start_time + min_duration
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                current_time = end_time
                current_location = location
                break
    
    # Now handle other friends in order of urgency
    for friend in sorted_friends:
        name, location, avail_start, avail_end, min_duration = friend
        if name == "James":
            continue  # already handled
        
        travel_time = travel_times[current_location].get(location, 0)
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        latest_start = avail_end_min - min_duration
        start_time = max(arrival_time, avail_start_min)
        
        if start_time <= latest_start:
            end_time = start_time + min_duration
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
            current_time = end_time
            current_location = location
    
    # Check if we missed any friends and try to fit them in
    scheduled_names = {meet["person"] for meet in itinerary}
    for friend in friends:
        name = friend[0]
        if name not in scheduled_names:
            # Try to fit this friend in
            name, location, avail_start, avail_end, min_duration = friend
            travel_time = travel_times[current_location].get(location, 0)
            arrival_time = current_time + travel_time
            avail_start_min = time_to_minutes(avail_start)
            avail_end_min = time_to_minutes(avail_end)
            latest_start = avail_end_min - min_duration
            start_time = max(arrival_time, avail_start_min)
            
            if start_time <= latest_start:
                end_time = start_time + min_duration
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": name,
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                current_time = end_time
                current_location = location
    
    return itinerary

def main():
    itinerary = generate_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()