import json

def time_to_minutes(time_str):
    parts = time_str.replace('AM', '').replace('PM', '').split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    if "PM" in time_str and hour != 12:
        hour += 12
    if "AM" in time_str and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    period = "AM" if hour < 12 else "PM"
    hour12 = hour % 12
    if hour12 == 0:
        hour12 = 12
    return f"{hour12}:{minute:02d}{period}"

def main():
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
    
    # Define friends
    joseph = {
        'name': 'Joseph',
        'location': "Fisherman's Wharf",
        'start': time_to_minutes("8:00AM"),
        'end': time_to_minutes("5:30PM"),
        'duration': 90
    }
    barbara = {
        'name': 'Barbara',
        'location': "Financial District",
        'start': time_to_minutes("10:30AM"),
        'end': time_to_minutes("4:30PM"),
        'duration': 15
    }
    kevin = {
        'name': 'Kevin',
        'location': "Mission District",
        'start': time_to_minutes("11:15AM"),
        'end': time_to_minutes("3:15PM"),
        'duration': 30
    }
    jeffrey = {
        'name': 'Jeffrey',
        'location': "Bayview",
        'start': time_to_minutes("5:30PM"),
        'end': time_to_minutes("9:30PM"),
        'duration': 60
    }
    
    # Start at Golden Gate Park at 9:00 AM
    start_location = "Golden Gate Park"
    start_time = time_to_minutes("9:00AM")
    joseph_fixed_start = time_to_minutes("3:30PM")
    joseph_fixed_end = joseph_fixed_start + joseph['duration']  # 5:00 PM
    
    # Permutations for Barbara and Kevin
    permutations = [
        [barbara, kevin], 
        [kevin, barbara]
    ]
    
    best_schedule = None
    min_travel = float('inf')
    
    for perm in permutations:
        current_loc = start_location
        current_time = start_time
        total_travel = 0
        schedule = []
        valid = True
        
        for friend in perm:
            tt = travel_times[current_loc][friend['location']]
            arrival = current_time + tt
            start_meeting = max(arrival, friend['start'])
            if start_meeting + friend['duration'] > friend['end']:
                valid = False
                break
            end_meeting = start_meeting + friend['duration']
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
        
        # Travel to Joseph
        tt_joseph = travel_times[current_loc][joseph['location']]
        arrival_joseph = current_time + tt_joseph
        total_travel += tt_joseph
        
        # Must arrive at Joseph by 3:30 PM
        if arrival_joseph > joseph_fixed_start:
            continue
        
        # Add Joseph meeting (fixed at 3:30PM-5:00PM)
        schedule.append({
            'name': joseph['name'],
            'location': joseph['location'],
            'start': joseph_fixed_start,
            'end': joseph_fixed_end
        })
        
        # Jeffrey meeting is fixed at 5:30PM-6:30PM
        # We leave Joseph's location at 5:00PM, travel time to Bayview is 26 min
        # Arrive at 5:26PM, then wait until 5:30PM to start
        
        # Update best schedule if this has less travel time
        if total_travel < min_travel:
            min_travel = total_travel
            best_schedule = schedule
    
    # Prepare final itinerary including Jeffrey
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
        # Add Jeffrey meeting
        itinerary.append({
            "action": "meet",
            "location": jeffrey['location'],
            "person": jeffrey['name'],
            "start_time": "5:30PM",
            "end_time": "6:30PM"
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()