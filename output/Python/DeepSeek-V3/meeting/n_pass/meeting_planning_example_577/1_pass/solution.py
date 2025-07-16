import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Locations
    locations = [
        "Haight-Ashbury", "Russian Hill", "Fisherman's Wharf", "Nob Hill",
        "Golden Gate Park", "Alamo Square", "Pacific Heights"
    ]
    
    # Travel times (in minutes) as a dictionary of dictionaries
    travel_times = {
        "Haight-Ashbury": {
            "Russian Hill": 17,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Alamo Square": 5,
            "Pacific Heights": 12
        },
        "Russian Hill": {
            "Haight-Ashbury": 17,
            "Fisherman's Wharf": 7,
            "Nob Hill": 5,
            "Golden Gate Park": 21,
            "Alamo Square": 15,
            "Pacific Heights": 7
        },
        "Fisherman's Wharf": {
            "Haight-Ashbury": 22,
            "Russian Hill": 7,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Alamo Square": 20,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Haight-Ashbury": 13,
            "Russian Hill": 5,
            "Fisherman's Wharf": 11,
            "Golden Gate Park": 17,
            "Alamo Square": 11,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Russian Hill": 19,
            "Fisherman's Wharf": 24,
            "Nob Hill": 20,
            "Alamo Square": 10,
            "Pacific Heights": 16
        },
        "Alamo Square": {
            "Haight-Ashbury": 5,
            "Russian Hill": 13,
            "Fisherman's Wharf": 19,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Haight-Ashbury": 11,
            "Russian Hill": 7,
            "Fisherman's Wharf": 13,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Alamo Square": 10
        }
    }
    
    # Friend constraints
    friends = [
        {
            "name": "Stephanie",
            "location": "Russian Hill",
            "start": "20:00",
            "end": "20:45",
            "min_duration": 15
        },
        {
            "name": "Kevin",
            "location": "Fisherman's Wharf",
            "start": "19:15",
            "end": "21:45",
            "min_duration": 75
        },
        {
            "name": "Robert",
            "location": "Nob Hill",
            "start": "7:45",
            "end": "10:30",
            "min_duration": 90
        },
        {
            "name": "Steven",
            "location": "Golden Gate Park",
            "start": "8:30",
            "end": "17:00",
            "min_duration": 75
        },
        {
            "name": "Anthony",
            "location": "Alamo Square",
            "start": "7:45",
            "end": "19:45",
            "min_duration": 15
        },
        {
            "name": "Sandra",
            "location": "Pacific Heights",
            "start": "14:45",
            "end": "21:45",
            "min_duration": 45
        }
    ]
    
    # Current time starts at 9:00 AM at Haight-Ashbury
    current_time = time_to_minutes("9:00")
    current_location = "Haight-Ashbury"
    
    # Filter friends who are available after current time
    available_friends = [f for f in friends if time_to_minutes(f["end"]) > current_time]
    
    # Generate all possible orders to meet friends
    best_schedule = []
    max_meetings = 0
    
    for order in permutations(available_friends):
        schedule = []
        temp_time = current_time
        temp_location = current_location
        meetings = 0
        
        for friend in order:
            # Calculate travel time
            travel_time = travel_times[temp_location][friend["location"]]
            arrival_time = temp_time + travel_time
            
            # Check if we can meet this friend
            friend_start = time_to_minutes(friend["start"])
            friend_end = time_to_minutes(friend["end"])
            
            # Adjust arrival time if we arrive before friend is available
            start_time = max(arrival_time, friend_start)
            
            # Calculate end time based on min duration
            end_time = start_time + friend["min_duration"]
            
            if end_time <= friend_end:
                # Add to schedule
                schedule.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time)
                })
                meetings += 1
                temp_time = end_time
                temp_location = friend["location"]
            else:
                # Can't meet this friend in this order
                break
        
        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule
    
    return {"itinerary": best_schedule}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))