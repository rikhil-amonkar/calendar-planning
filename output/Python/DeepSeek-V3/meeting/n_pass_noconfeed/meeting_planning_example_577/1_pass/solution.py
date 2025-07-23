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
        "Haight-Ashbury",
        "Russian Hill",
        "Fisherman's Wharf",
        "Nob Hill",
        "Golden Gate Park",
        "Alamo Square",
        "Pacific Heights"
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
    
    # Friends' availability
    friends = [
        {
            "name": "Stephanie",
            "location": "Russian Hill",
            "start": "20:00",
            "end": "20:45",
            "duration": 15
        },
        {
            "name": "Kevin",
            "location": "Fisherman's Wharf",
            "start": "19:15",
            "end": "21:45",
            "duration": 75
        },
        {
            "name": "Robert",
            "location": "Nob Hill",
            "start": "7:45",
            "end": "10:30",
            "duration": 90
        },
        {
            "name": "Steven",
            "location": "Golden Gate Park",
            "start": "8:30",
            "end": "17:00",
            "duration": 75
        },
        {
            "name": "Anthony",
            "location": "Alamo Square",
            "start": "7:45",
            "end": "19:45",
            "duration": 15
        },
        {
            "name": "Sandra",
            "location": "Pacific Heights",
            "start": "14:45",
            "end": "21:45",
            "duration": 45
        }
    ]
    
    # Current time starts at Haight-Ashbury at 9:00
    current_time = time_to_minutes("9:00")
    current_location = "Haight-Ashbury"
    
    # Sort friends by earliest possible meeting time
    friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x["start"]))
    
    itinerary = []
    
    # Try to meet Robert first (earliest availability)
    robert = next(f for f in friends_sorted if f["name"] == "Robert")
    travel_time = travel_times[current_location][robert["location"]]
    arrival_time = current_time + travel_time
    robert_start = time_to_minutes(robert["start"])
    robert_end = time_to_minutes(robert["end"])
    
    if arrival_time <= robert_end - robert["duration"]:
        meet_start = max(arrival_time, robert_start)
        meet_end = meet_start + robert["duration"]
        itinerary.append({
            "action": "meet",
            "location": robert["location"],
            "person": robert["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = robert["location"]
    
    # Next, try to meet Steven
    steven = next(f for f in friends_sorted if f["name"] == "Steven")
    travel_time = travel_times[current_location][steven["location"]]
    arrival_time = current_time + travel_time
    steven_start = time_to_minutes(steven["start"])
    steven_end = time_to_minutes(steven["end"])
    
    if arrival_time <= steven_end - steven["duration"]:
        meet_start = max(arrival_time, steven_start)
        meet_end = meet_start + steven["duration"]
        itinerary.append({
            "action": "meet",
            "location": steven["location"],
            "person": steven["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = steven["location"]
    
    # Next, try to meet Anthony
    anthony = next(f for f in friends_sorted if f["name"] == "Anthony")
    travel_time = travel_times[current_location][anthony["location"]]
    arrival_time = current_time + travel_time
    anthony_start = time_to_minutes(anthony["start"])
    anthony_end = time_to_minutes(anthony["end"])
    
    if arrival_time <= anthony_end - anthony["duration"]:
        meet_start = max(arrival_time, anthony_start)
        meet_end = meet_start + anthony["duration"]
        itinerary.append({
            "action": "meet",
            "location": anthony["location"],
            "person": anthony["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = anthony["location"]
    
    # Next, try to meet Sandra
    sandra = next(f for f in friends_sorted if f["name"] == "Sandra")
    travel_time = travel_times[current_location][sandra["location"]]
    arrival_time = current_time + travel_time
    sandra_start = time_to_minutes(sandra["start"])
    sandra_end = time_to_minutes(sandra["end"])
    
    if arrival_time <= sandra_end - sandra["duration"]:
        meet_start = max(arrival_time, sandra_start)
        meet_end = meet_start + sandra["duration"]
        itinerary.append({
            "action": "meet",
            "location": sandra["location"],
            "person": sandra["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = sandra["location"]
    
    # Next, try to meet Kevin
    kevin = next(f for f in friends_sorted if f["name"] == "Kevin")
    travel_time = travel_times[current_location][kevin["location"]]
    arrival_time = current_time + travel_time
    kevin_start = time_to_minutes(kevin["start"])
    kevin_end = time_to_minutes(kevin["end"])
    
    if arrival_time <= kevin_end - kevin["duration"]:
        meet_start = max(arrival_time, kevin_start)
        meet_end = meet_start + kevin["duration"]
        itinerary.append({
            "action": "meet",
            "location": kevin["location"],
            "person": kevin["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = kevin["location"]
    
    # Finally, try to meet Stephanie
    stephanie = next(f for f in friends_sorted if f["name"] == "Stephanie")
    travel_time = travel_times[current_location][stephanie["location"]]
    arrival_time = current_time + travel_time
    stephanie_start = time_to_minutes(stephanie["start"])
    stephanie_end = time_to_minutes(stephanie["end"])
    
    if arrival_time <= stephanie_end - stephanie["duration"]:
        meet_start = max(arrival_time, stephanie_start)
        meet_end = meet_start + stephanie["duration"]
        itinerary.append({
            "action": "meet",
            "location": stephanie["location"],
            "person": stephanie["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))