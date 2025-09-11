import itertools
import json

def main():
    # Travel times dictionary
    travel_times = {
        "Marina District": {
            "Marina District": 0,
            "Richmond District": 11,
            "Union Square": 16,
            "Nob Hill": 12,
            "Fisherman's Wharf": 10,
            "Golden Gate Park": 18,
            "Embarcadero": 14,
            "Financial District": 17,
            "North Beach": 11,
            "Presidio": 10
        },
        "Richmond District": {
            "Marina District": 9,
            "Richmond District": 0,
            "Union Square": 21,
            "Nob Hill": 17,
            "Fisherman's Wharf": 18,
            "Golden Gate Park": 9,
            "Embarcadero": 19,
            "Financial District": 22,
            "North Beach": 17,
            "Presidio": 7
        },
        "Union Square": {
            "Marina District": 18,
            "Richmond District": 20,
            "Union Square": 0,
            "Nob Hill": 9,
            "Fisherman's Wharf": 15,
            "Golden Gate Park": 22,
            "Embarcadero": 11,
            "Financial District": 9,
            "North Beach": 10,
            "Presidio": 24
        },
        "Nob Hill": {
            "Marina District": 11,
            "Richmond District": 14,
            "Union Square": 7,
            "Nob Hill": 0,
            "Fisherman's Wharf": 10,
            "Golden Gate Park": 17,
            "Embarcadero": 9,
            "Financial District": 9,
            "North Beach": 8,
            "Presidio": 17
        },
        "Fisherman's Wharf": {
            "Marina District": 9,
            "Richmond District": 18,
            "Union Square": 13,
            "Nob Hill": 11,
            "Fisherman's Wharf": 0,
            "Golden Gate Park": 25,
            "Embarcadero": 8,
            "Financial District": 11,
            "North Beach": 6,
            "Presidio": 17
        },
        "Golden Gate Park": {
            "Marina District": 16,
            "Richmond District": 7,
            "Union Square": 22,
            "Nob Hill": 20,
            "Fisherman's Wharf": 24,
            "Golden Gate Park": 0,
            "Embarcadero": 25,
            "Financial District": 26,
            "North Beach": 23,
            "Presidio": 11
        },
        "Embarcadero": {
            "Marina District": 12,
            "Richmond District": 21,
            "Union Square": 10,
            "Nob Hill": 10,
            "Fisherman's Wharf": 6,
            "Golden Gate Park": 25,
            "Embarcadero": 0,
            "Financial District": 5,
            "North Beach": 5,
            "Presidio": 20
        },
        "Financial District": {
            "Marina District": 15,
            "Richmond District": 21,
            "Union Square": 9,
            "Nob Hill": 8,
            "Fisherman's Wharf": 10,
            "Golden Gate Park": 23,
            "Embarcadero": 4,
            "Financial District": 0,
            "North Beach": 7,
            "Presidio": 22
        },
        "North Beach": {
            "Marina District": 9,
            "Richmond District": 18,
            "Union Square": 7,
            "Nob Hill": 7,
            "Fisherman's Wharf": 5,
            "Golden Gate Park": 22,
            "Embarcadero": 6,
            "Financial District": 8,
            "North Beach": 0,
            "Presidio": 17
        },
        "Presidio": {
            "Marina District": 11,
            "Richmond District": 7,
            "Union Square": 22,
            "Nob Hill": 18,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 12,
            "Embarcadero": 20,
            "Financial District": 23,
            "North Beach": 18,
            "Presidio": 0
        }
    }
    
    # Friends data with times converted to minutes from midnight
    friends = [
        {
            "name": "Stephanie",
            "location": "Richmond District",
            "start_available": 16 * 60 + 15,  # 4:15PM
            "end_available": 21 * 60 + 30,    # 9:30PM
            "duration": 75
        },
        {
            "name": "William",
            "location": "Union Square",
            "start_available": 10 * 60 + 45,  # 10:45AM
            "end_available": 17 * 60 + 30,    # 5:30PM
            "duration": 45
        },
        {
            "name": "Elizabeth",
            "location": "Nob Hill",
            "start_available": 12 * 60 + 15,  # 12:15PM
            "end_available": 15 * 60 + 0,     # 3:00PM
            "duration": 105
        },
        {
            "name": "Joseph",
            "location": "Fisherman's Wharf",
            "start_available": 12 * 60 + 45,  # 12:45PM
            "end_available": 14 * 60 + 0,     # 2:00PM
            "duration": 75
        },
        {
            "name": "Anthony",
            "location": "Golden Gate Park",
            "start_available": 13 * 60 + 0,   # 1:00PM
            "end_available": 20 * 60 + 30,    # 8:30PM
            "duration": 75
        },
        {
            "name": "Barbara",
            "location": "Embarcadero",
            "start_available": 19 * 60 + 15,  # 7:15PM
            "end_available": 20 * 60 + 30,    # 8:30PM
            "duration": 75
        },
        {
            "name": "Carol",
            "location": "Financial District",
            "start_available": 11 * 60 + 45,  # 11:45AM
            "end_available": 16 * 60 + 15,    # 4:15PM
            "duration": 60
        },
        {
            "name": "Sandra",
            "location": "North Beach",
            "start_available": 10 * 60 + 0,   # 10:00AM
            "end_available": 12 * 60 + 30,    # 12:30PM
            "duration": 15
        },
        {
            "name": "Kenneth",
            "location": "Presidio",
            "start_available": 21 * 60 + 15,  # 9:15PM
            "end_available": 22 * 60 + 15,    # 10:15PM
            "duration": 45
        }
    ]
    
    start_time = 9 * 60  # 9:00AM in minutes
    start_location = "Marina District"
    
    best_count = 0
    best_schedule = []
    
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        meetings = []
        
        for friend in perm:
            loc = friend["location"]
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time
            
            if arrival_time > friend["end_available"]:
                continue
                
            start_meeting = max(arrival_time, friend["start_available"])
            end_meeting = start_meeting + friend["duration"]
            
            if end_meeting <= friend["end_available"]:
                meetings.append({
                    "friend": friend,
                    "start": start_meeting,
                    "end": end_meeting
                })
                current_time = end_meeting
                current_location = loc
        
        if len(meetings) > best_count:
            best_count = len(meetings)
            best_schedule = meetings
    
    # Convert best schedule to output format
    itinerary = []
    for meeting in best_schedule:
        friend = meeting["friend"]
        start_minutes = meeting["start"]
        end_minutes = meeting["end"]
        
        # Convert minutes to time string
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": start_str,
            "end_time": end_str
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()