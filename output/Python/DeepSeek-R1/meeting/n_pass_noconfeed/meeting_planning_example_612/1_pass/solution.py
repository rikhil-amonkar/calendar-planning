import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours}:{minutes_part:02d}"

def main():
    travel_times = {
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Embarcadero'): 31,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Embarcadero'): 25
    }
    
    friends = [
        {'name': 'Emily', 'location': 'Russian Hill', 'start': 735, 'end': 855, 'min_duration': 105},
        {'name': 'Mark', 'location': 'Presidio', 'start': 1005, 'end': 1170, 'min_duration': 60},
        {'name': 'Deborah', 'location': 'Chinatown', 'start': 450, 'end': 930, 'min_duration': 45},
        {'name': 'Margaret', 'location': 'Sunset District', 'start': 1290, 'end': 1350, 'min_duration': 60},
        {'name': 'George', 'location': 'The Castro', 'start': 450, 'end': 855, 'min_duration': 60},
        {'name': 'Andrew', 'location': 'Embarcadero', 'start': 1215, 'end': 1320, 'min_duration': 75},
        {'name': 'Steven', 'location': 'Golden Gate Park', 'start': 675, 'end': 1275, 'min_duration': 105}
    ]
    
    start_time = 540
    start_location = 'Alamo Square'
    max_count = 0
    best_itinerary = None
    
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        count = 0
        
        for friend in perm:
            if current_location == friend['location']:
                travel = 0
            else:
                key = (current_location, friend['location'])
                travel = travel_times.get(key, 10**9)
                
            arrival_time = current_time + travel
            start_meeting = max(arrival_time, friend['start'])
            end_meeting = start_meeting + friend['min_duration']
            
            if end_meeting <= friend['end']:
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_meeting),
                    'end_time': minutes_to_time(end_meeting)
                })
                current_time = end_meeting
                current_location = friend['location']
                count += 1
            else:
                continue
                
        if count > max_count:
            max_count = count
            best_itinerary = itinerary
            if max_count == len(friends):
                break
                
    if best_itinerary is None:
        best_itinerary = []
        
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()