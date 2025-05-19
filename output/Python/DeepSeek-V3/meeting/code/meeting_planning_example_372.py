import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Golden Gate Park': 11,
        'Mission District': 24
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Golden Gate Park': 9,
        'Mission District': 10
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Golden Gate Park': 21,
        'Mission District': 16
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Mission District': 17
    },
    'Mission District': {
        'Sunset District': 24,
        'Alamo Square': 11,
        'Russian Hill': 15,
        'Golden Gate Park': 17
    }
}

# Friend availability
friends = {
    'Charles': {
        'location': 'Alamo Square',
        'start': 18 * 60,  # 6:00 PM in minutes
        'end': 20 * 60 + 45,  # 8:45 PM in minutes
        'duration': 90  # minutes
    },
    'Margaret': {
        'location': 'Russian Hill',
        'start': 9 * 60,  # 9:00 AM in minutes
        'end': 16 * 60,  # 4:00 PM in minutes
        'duration': 30  # minutes
    },
    'Daniel': {
        'location': 'Golden Gate Park',
        'start': 8 * 60,  # 8:00 AM in minutes
        'end': 13 * 60 + 30,  # 1:30 PM in minutes
        'duration': 15  # minutes
    },
    'Stephanie': {
        'location': 'Mission District',
        'start': 20 * 60 + 30,  # 8:30 PM in minutes
        'end': 22 * 60,  # 10:00 PM in minutes
        'duration': 90  # minutes
    }
}

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_best_schedule():
    best_schedule = None
    max_meetings = 0
    
    # Try all possible orders of meeting friends
    for order in permutations(friends.keys()):
        current_location = 'Sunset District'
        current_time = 9 * 60  # 9:00 AM
        schedule = []
        meetings = 0
        
        for person in order:
            friend = friends[person]
            location = friend['location']
            travel_time = travel_times[current_location][location]
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['duration']
            
            if meeting_end > friend['end']:
                # Can't meet this friend in this order
                break
                
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': person,
                'start_time': time_to_str(meeting_start),
                'end_time': time_to_str(meeting_end)
            })
            
            current_time = meeting_end
            current_location = location
            meetings += 1
        
        if meetings > max_meetings or (meetings == max_meetings and current_time < best_schedule['end_time']):
            max_meetings = meetings
            best_schedule = {
                'itinerary': schedule,
                'end_time': current_time
            }
    
    return best_schedule['itinerary'] if best_schedule else []

def main():
    itinerary = find_best_schedule()
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == "__main__":
    main()