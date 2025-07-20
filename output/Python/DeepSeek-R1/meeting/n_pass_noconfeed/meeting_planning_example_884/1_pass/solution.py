import json

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        'Richmond District': {'Chinatown': 20, 'Sunset District': 11, 'Alamo Square': 13, 'Financial District': 22, 'North Beach': 17, 'Embarcadero': 19, 'Presidio': 7, 'Golden Gate Park': 9, 'Bayview': 27},
        'Chinatown': {'Richmond District': 20, 'Sunset District': 29, 'Alamo Square': 17, 'Financial District': 5, 'North Beach': 3, 'Embarcadero': 5, 'Presidio': 19, 'Golden Gate Park': 23, 'Bayview': 20},
        'Sunset District': {'Richmond District': 12, 'Chinatown': 30, 'Alamo Square': 17, 'Financial District': 30, 'North Beach': 28, 'Embarcadero': 30, 'Presidio': 16, 'Golden Gate Park': 11, 'Bayview': 22},
        'Alamo Square': {'Richmond District': 11, 'Chinatown': 15, 'Sunset District': 16, 'Financial District': 17, 'North Beach': 15, 'Embarcadero': 16, 'Presidio': 17, 'Golden Gate Park': 9, 'Bayview': 16},
        'Financial District': {'Richmond District': 21, 'Chinatown': 5, 'Sunset District': 30, 'Alamo Square': 17, 'North Beach': 7, 'Embarcadero': 4, 'Presidio': 22, 'Golden Gate Park': 23, 'Bayview': 19},
        'North Beach': {'Richmond District': 18, 'Chinatown': 6, 'Sunset District': 27, 'Alamo Square': 16, 'Financial District': 8, 'Embarcadero': 6, 'Presidio': 17, 'Golden Gate Park': 22, 'Bayview': 25},
        'Embarcadero': {'Richmond District': 21, 'Chinatown': 7, 'Sunset District': 30, 'Alamo Square': 19, 'Financial District': 5, 'North Beach': 5, 'Presidio': 20, 'Golden Gate Park': 25, 'Bayview': 21},
        'Presidio': {'Richmond District': 7, 'Chinatown': 21, 'Sunset District': 15, 'Alamo Square': 19, 'Financial District': 23, 'North Beach': 18, 'Embarcadero': 20, 'Golden Gate Park': 12, 'Bayview': 31},
        'Golden Gate Park': {'Richmond District': 7, 'Chinatown': 23, 'Sunset District': 10, 'Alamo Square': 9, 'Financial District': 26, 'North Beach': 23, 'Embarcadero': 25, 'Presidio': 11, 'Bayview': 22},
        'Bayview': {'Richmond District': 25, 'Chinatown': 19, 'Sunset District': 23, 'Alamo Square': 16, 'Financial District': 19, 'North Beach': 22, 'Embarcadero': 19, 'Presidio': 32, 'Golden Gate Park': 22}
    }
    
    meetings_in_order = [
        {'person': 'Matthew', 'location': 'Alamo Square', 'min_duration': 90, 'available_start': 525, 'available_end': 825},
        {'person': 'Melissa', 'location': 'North Beach', 'min_duration': 45, 'available_start': 435, 'available_end': 1005},
        {'person': 'Robert', 'location': 'Chinatown', 'min_duration': 120, 'available_start': 465, 'available_end': 1050},
        {'person': 'David', 'location': 'Sunset District', 'min_duration': 45, 'available_start': 750, 'available_end': 1185},
        {'person': 'Mark', 'location': 'Embarcadero', 'min_duration': 45, 'available_start': 915, 'available_end': 1020},
        {'person': 'Jessica', 'location': 'Financial District', 'min_duration': 45, 'available_start': 570, 'available_end': 1125},
        {'person': 'Deborah', 'location': 'Presidio', 'min_duration': 45, 'available_start': 1140, 'available_end': 1185},
        {'person': 'Karen', 'location': 'Golden Gate Park', 'min_duration': 120, 'available_start': 1170, 'available_end': 1320}
    ]
    
    current_location = 'Richmond District'
    current_time = 540
    itinerary = []
    
    for meeting in meetings_in_order:
        travel_duration = travel_times[current_location][meeting['location']]
        current_time += travel_duration
        start_time = max(current_time, meeting['available_start'])
        end_time = start_time + meeting['min_duration']
        current_time = end_time
        current_location = meeting['location']
        
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()