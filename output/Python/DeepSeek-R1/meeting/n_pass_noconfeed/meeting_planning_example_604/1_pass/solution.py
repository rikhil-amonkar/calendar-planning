import json

def time_to_minutes(time_str):
    if time_str.endswith('AM') or time_str.endswith('PM'):
        time_part = time_str[:-2].strip()
        period = time_str[-2:]
    else:
        time_part = time_str
        period = None
    
    hour, minute = map(int, time_part.split(':'))
    
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Fisherman's Wharf": {
            "The Castro": 26,
            "Golden Gate Park": 25,
            "Embarcadero": 8,
            "Russian Hill": 7,
            "Nob Hill": 11,
            "Alamo Square": 20,
            "North Beach": 6
        },
        "The Castro": {
            "Fisherman's Wharf": 24,
            "Golden Gate Park": 11,
            "Embarcadero": 22,
            "Russian Hill": 18,
            "Nob Hill": 16,
            "Alamo Square": 8,
            "North Beach": 20
        },
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "The Castro": 13,
            "Embarcadero": 25,
            "Russian Hill": 19,
            "Nob Hill": 20,
            "Alamo Square": 10,
            "North Beach": 24
        },
        "Embarcadero": {
            "Fisherman's Wharf": 6,
            "The Castro": 25,
            "Golden Gate Park": 25,
            "Russian Hill": 8,
            "Nob Hill": 10,
            "Alamo Square": 19,
            "North Beach": 5
        },
        "Russian Hill": {
            "Fisherman's Wharf": 7,
            "The Castro": 21,
            "Golden Gate Park": 21,
            "Embarcadero": 8,
            "Nob Hill": 5,
            "Alamo Square": 15,
            "North Beach": 5
        },
        "Nob Hill": {
            "Fisherman's Wharf": 11,
            "The Castro": 17,
            "Golden Gate Park": 17,
            "Embarcadero": 9,
            "Russian Hill": 5,
            "Alamo Square": 11,
            "North Beach": 8
        },
        "Alamo Square": {
            "Fisherman's Wharf": 19,
            "The Castro": 8,
            "Golden Gate Park": 9,
            "Embarcadero": 17,
            "Russian Hill": 13,
            "Nob Hill": 11,
            "North Beach": 15
        },
        "North Beach": {
            "Fisherman's Wharf": 5,
            "The Castro": 22,
            "Golden Gate Park": 22,
            "Embarcadero": 6,
            "Russian Hill": 4,
            "Nob Hill": 7,
            "Alamo Square": 16
        }
    }

    friends = [
        {"name": "Laura", "location": "The Castro", "start": "7:45PM", "end": "9:30PM", "min_duration": 105},
        {"name": "Daniel", "location": "Golden Gate Park", "start": "9:15PM", "end": "9:45PM", "min_duration": 15},
        {"name": "William", "location": "Embarcadero", "start": "7:00AM", "end": "9:00AM", "min_duration": 90},
        {"name": "Karen", "location": "Russian Hill", "start": "2:30PM", "end": "7:45PM", "min_duration": 30},
        {"name": "Stephanie", "location": "Nob Hill", "start": "7:30AM", "end": "9:30AM", "min_duration": 45},
        {"name": "Joseph", "location": "Alamo Square", "start": "11:30AM", "end": "12:45PM", "min_duration": 15},
        {"name": "Kimberly", "location": "North Beach", "start": "3:45PM", "end": "7:15PM", "min_duration": 30}
    ]
    
    for friend in friends:
        friend['start_min'] = time_to_minutes(friend['start'])
        friend['end_min'] = time_to_minutes(friend['end'])
    
    sorted_friends = sorted(friends, key=lambda x: x['start_min'])
    
    current_time = time_to_minutes("9:00AM")
    current_location = "Fisherman's Wharf"
    itinerary = []
    
    for friend in sorted_friends:
        if current_location == friend['location']:
            travel_time = 0
        else:
            travel_time = travel_times[current_location][friend['location']]
        
        arrival_time = current_time + travel_time
        
        if arrival_time > friend['end_min']:
            continue
        
        meeting_start = max(arrival_time, friend['start_min'])
        meeting_end = meeting_start + friend['min_duration']
        
        if meeting_end > friend['end_min']:
            continue
        
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = friend['location']
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()