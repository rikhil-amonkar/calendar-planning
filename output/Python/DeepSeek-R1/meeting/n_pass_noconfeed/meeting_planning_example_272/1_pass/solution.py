import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    mins = minutes_val % 60
    return f"{hours}:{mins:02d}"

def main():
    start_time_str = '9:00'
    start_location = 'Russian Hill'
    
    friends_data = [
        {'name': 'Timothy', 'location': 'Embarcadero', 'available_start': '9:45', 'available_end': '17:45', 'min_duration': 120},
        {'name': 'Patricia', 'location': 'Nob Hill', 'available_start': '18:30', 'available_end': '21:45', 'min_duration': 90},
        {'name': 'Ashley', 'location': 'Mission District', 'available_start': '20:30', 'available_end': '21:15', 'min_duration': 45}
    ]
    
    travel_times = {
        'Russian Hill': {'Nob Hill': 5, 'Mission District': 16, 'Embarcadero': 8},
        'Nob Hill': {'Russian Hill': 5, 'Mission District': 13, 'Embarcadero': 9},
        'Mission District': {'Russian Hill': 15, 'Nob Hill': 12, 'Embarcadero': 19},
        'Embarcadero': {'Russian Hill': 8, 'Nob Hill': 10, 'Mission District': 20}
    }
    
    for friend in friends_data:
        friend['available_start_minutes'] = time_to_minutes(friend['available_start'])
        friend['available_end_minutes'] = time_to_minutes(friend['available_end'])
    
    start_time_minutes = time_to_minutes(start_time_str)
    
    best_schedule = []
    best_count = 0
    
    for perm in itertools.permutations(friends_data):
        current_time = start_time_minutes
        current_loc = start_location
        scheduled = []
        
        for friend in perm:
            if current_loc == friend['location']:
                travel_time = 0
            else:
                travel_time = travel_times[current_loc][friend['location']]
            
            arrival = current_time + travel_time
            start_meeting = max(arrival, friend['available_start_minutes'])
            end_meeting = start_meeting + friend['min_duration']
            
            if end_meeting <= friend['available_end_minutes']:
                scheduled.append({
                    'person': friend['name'],
                    'location': friend['location'],
                    'start_time': start_meeting,
                    'end_time': end_meeting
                })
                current_time = end_meeting
                current_loc = friend['location']
        
        if len(scheduled) > best_count:
            best_count = len(scheduled)
            best_schedule = scheduled
    
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": minutes_to_time(meeting['start_time']),
            "end_time": minutes_to_time(meeting['end_time'])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()