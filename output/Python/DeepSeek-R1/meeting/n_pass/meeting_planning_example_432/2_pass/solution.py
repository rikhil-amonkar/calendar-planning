import json
import itertools
from collections import defaultdict

def main():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Mission District": 17,
            "Embarcadero": 25,
            "Financial District": 26
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Bayview": 26,
            "Mission District": 22,
            "Embarcadero": 8,
            "Financial District": 11
        },
        "Bayview": {
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 25,
            "Mission District": 13,
            "Embarcadero": 19,
            "Financial District": 19
        },
        "Mission District": {
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 22,
            "Bayview": 15,
            "Embarcadero": 19,
            "Financial District": 17
        },
        "Embarcadero": {
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Mission District": 20,
            "Financial District": 5
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 10,
            "Bayview": 19,
            "Mission District": 17,
            "Embarcadero": 4
        }
    }
    
    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.replace('AM', '').replace('PM', '').split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        if "PM" in time_str and hour != 12:
            hour += 12
        if "AM" in time_str and hour == 12:
            hour = 0
        return hour * 60 + minute

    # Define friends and their constraints (excluding David and Jeffrey for permutation)
    friends = [
        {'name': 'Joseph', 'location': "Fisherman's Wharf", 'start': time_to_minutes("8:00AM"), 'end': time_to_minutes("5:30PM"), 'duration': 90},
        {'name': 'Barbara', 'location': "Financial District", 'start': time_to_minutes("10:30AM"), 'end': time_to_minutes("4:30PM"), 'duration': 15},
        {'name': 'Kevin', 'location': "Mission District", 'start': time_to_minutes("11:15AM"), 'end': time_to_minutes("3:15PM"), 'duration': 30}
    ]
    
    # Jeffrey is fixed as the last meeting
    jeffrey = {'name': 'Jeffrey', 'location': "Bayview", 'start': time_to_minutes("5:30PM"), 'end': time_to_minutes("9:30PM"), 'duration': 60}
    
    # Start at Golden Gate Park at 9:00 AM
    start_location = "Golden Gate Park"
    start_time = time_to_minutes("9:00AM")
    
    # Generate permutations for the three friends
    permutations = list(itertools.permutations(friends))
    best_schedule = None
    min_travel = float('inf')
    
    for perm in permutations:
        current_loc = start_location
        current_time = start_time
        total_travel = 0
        schedule = []
        valid = True
        
        # Schedule the three friends in this permutation
        for friend in perm:
            # Get travel time to friend's location
            tt = travel_times[current_loc][friend['location']]
            arrival = current_time + tt
            # Start meeting at the later of arrival or friend's available start time
            start_meeting = max(arrival, friend['start'])
            # Check if meeting fits within friend's window
            if start_meeting + friend['duration'] > friend['end']:
                valid = False
                break
            end_meeting = start_meeting + friend['duration']
            # Record meeting details
            schedule.append({
                'name': friend['name'],
                'location': friend['location'],
                'start': start_meeting,
                'end': end_meeting
            })
            total_travel += tt
            current_time = end_meeting
            current_loc = friend['location']
        
        if not valid:
            continue
        
        # Schedule Jeffrey last
        tt_jeff = travel_times[current_loc][jeffrey['location']]
        # Must leave early enough to arrive by 5:30 PM (1050 minutes)
        if current_time <= jeffrey['start'] - tt_jeff:
            # Meeting Jeffrey starts at 5:30 PM
            start_jeff = jeffrey['start']
            end_jeff = start_jeff + jeffrey['duration']
            if end_jeff <= jeffrey['end']:
                schedule.append({
                    'name': jeffrey['name'],
                    'location': jeffrey['location'],
                    'start': start_jeff,
                    'end': end_jeff
                })
                total_travel += tt_jeff
                # Update best schedule if this has less travel time
                if total_travel < min_travel:
                    min_travel = total_travel
                    best_schedule = schedule
    
    # Convert best schedule to output format
    def minutes_to_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    itinerary = []
    if best_schedule:
        for meeting in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['name'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()