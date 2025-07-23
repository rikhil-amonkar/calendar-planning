import json
from datetime import datetime, timedelta

# Travel times dictionary
travel_times = {
    "Mission District": {
        "Alamo Square": 11,
        "Presidio": 25,
        "Russian Hill": 15,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Financial District": 15,
        "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10,
        "Presidio": 17,
        "Russian Hill": 13,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Embarcadero": 16,
        "Financial District": 17,
        "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26,
        "Alamo Square": 19,
        "Russian Hill": 14,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Financial District": 23,
        "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16,
        "Alamo Square": 15,
        "Presidio": 14,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18,
        "Alamo Square": 16,
        "Presidio": 17,
        "Russian Hill": 4,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Financial District": 8,
        "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "Alamo Square": 9,
        "Presidio": 11,
        "Russian Hill": 19,
        "North Beach": 23,
        "Richmond District": 7,
        "Embarcadero": 25,
        "Financial District": 26,
        "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20,
        "Alamo Square": 13,
        "Presidio": 7,
        "Russian Hill": 13,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20,
        "Alamo Square": 19,
        "Presidio": 20,
        "Russian Hill": 8,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17,
        "Alamo Square": 17,
        "Presidio": 22,
        "Russian Hill": 11,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Embarcadero": 4,
        "Marina District": 17
    },
    "Marina District": {
        "Mission District": 20,
        "Alamo Square": 15,
        "Presidio": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Financial District": 17
    }
}

# Friend constraints
friends = [
    {"name": "Laura", "location": "Alamo Square", "start": "14:30", "end": "16:15", "duration": 75},
    {"name": "Brian", "location": "Presidio", "start": "10:15", "end": "17:00", "duration": 30},
    {"name": "Karen", "location": "Russian Hill", "start": "18:00", "end": "20:15", "duration": 90},
    {"name": "Stephanie", "location": "North Beach", "start": "10:15", "end": "16:00", "duration": 75},
    {"name": "Helen", "location": "Golden Gate Park", "start": "11:30", "end": "21:45", "duration": 120},
    {"name": "Sandra", "location": "Richmond District", "start": "8:00", "end": "15:15", "duration": 30},
    {"name": "Mary", "location": "Embarcadero", "start": "16:45", "end": "18:45", "duration": 120},
    {"name": "Deborah", "location": "Financial District", "start": "19:00", "end": "20:45", "duration": 105},
    {"name": "Elizabeth", "location": "Marina District", "start": "8:30", "end": "13:15", "duration": 105}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    if from_loc == to_loc:
        return 0
    try:
        return travel_times[from_loc][to_loc]
    except KeyError:
        return travel_times[to_loc][from_loc]

def find_best_schedule():
    current_time = time_to_minutes("9:00")
    current_location = "Mission District"
    schedule = []
    remaining_friends = friends.copy()
    
    while remaining_friends:
        best_friend = None
        best_start_time = None
        best_end_time = None
        best_travel_time = float('inf')
        
        for friend in remaining_friends:
            travel_time = get_travel_time(current_location, friend["location"])
            arrival_time = current_time + travel_time
            friend_start = time_to_minutes(friend["start"])
            friend_end = time_to_minutes(friend["end"])
            
            # Calculate possible meeting time
            meeting_start = max(arrival_time, friend_start)
            meeting_end = meeting_start + friend["duration"]
            
            # Check if meeting is possible
            if meeting_end <= friend_end:
                # Check for overlaps with existing schedule
                overlap = False
                for event in schedule:
                    event_start = time_to_minutes(event["start_time"])
                    event_end = time_to_minutes(event["end_time"])
                    if not (meeting_end <= event_start or meeting_start >= event_end):
                        overlap = True
                        break
                
                if not overlap:
                    # Prefer friend with earliest possible meeting time
                    if meeting_start < best_start_time if best_start_time else True:
                        best_friend = friend
                        best_start_time = meeting_start
                        best_end_time = meeting_end
                        best_travel_time = travel_time
        
        if best_friend:
            schedule.append({
                "action": "meet",
                "location": best_friend["location"],
                "person": best_friend["name"],
                "start_time": minutes_to_time(best_start_time),
                "end_time": minutes_to_time(best_end_time)
            })
            current_location = best_friend["location"]
            current_time = best_end_time
            remaining_friends.remove(best_friend)
        else:
            # No valid friend to meet next, break the loop
            break
    
    return schedule

def main():
    schedule = find_best_schedule()
    
    # Convert to JSON format
    result = {
        "itinerary": schedule
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()