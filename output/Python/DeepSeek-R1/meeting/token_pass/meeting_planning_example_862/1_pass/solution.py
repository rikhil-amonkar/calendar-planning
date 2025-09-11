import json

def main():
    # Travel times in minutes between locations
    travel_time = {
        'Mission District': {'Mission District': 0, 'Alamo Square': 11, 'Presidio': 25, 'Russian Hill': 15, 'North Beach': 17, 'Golden Gate Park': 17, 'Richmond District': 20, 'Embarcadero': 19, 'Financial District': 15, 'Marina District': 19},
        'Alamo Square': {'Mission District': 10, 'Alamo Square': 0, 'Presidio': 17, 'Russian Hill': 13, 'North Beach': 15, 'Golden Gate Park': 9, 'Richmond District': 11, 'Embarcadero': 16, 'Financial District': 17, 'Marina District': 15},
        'Presidio': {'Mission District': 26, 'Alamo Square': 19, 'Presidio': 0, 'Russian Hill': 14, 'North Beach': 18, 'Golden Gate Park': 12, 'Richmond District': 7, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11},
        'Russian Hill': {'Mission District': 16, 'Alamo Square': 15, 'Presidio': 14, 'Russian Hill': 0, 'North Beach': 5, 'Golden Gate Park': 21, 'Richmond District': 14, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7},
        'North Beach': {'Mission District': 18, 'Alamo Square': 16, 'Presidio': 17, 'Russian Hill': 4, 'North Beach': 0, 'Golden Gate Park': 22, 'Richmond District': 18, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9},
        'Golden Gate Park': {'Mission District': 17, 'Alamo Square': 9, 'Presidio': 11, 'Russian Hill': 19, 'North Beach': 23, 'Golden Gate Park': 0, 'Richmond District': 7, 'Embarcadero': 25, 'Financial District': 26, 'Marina District': 16},
        'Richmond District': {'Mission District': 20, 'Alamo Square': 13, 'Presidio': 7, 'Russian Hill': 13, 'North Beach': 17, 'Golden Gate Park': 9, 'Richmond District': 0, 'Embarcadero': 19, 'Financial District': 22, 'Marina District': 9},
        'Embarcadero': {'Mission District': 20, 'Alamo Square': 19, 'Presidio': 20, 'Russian Hill': 8, 'North Beach': 5, 'Golden Gate Park': 25, 'Richmond District': 21, 'Embarcadero': 0, 'Financial District': 5, 'Marina District': 12},
        'Financial District': {'Mission District': 17, 'Alamo Square': 17, 'Presidio': 22, 'Russian Hill': 11, 'North Beach': 7, 'Golden Gate Park': 23, 'Richmond District': 21, 'Embarcadero': 4, 'Financial District': 0, 'Marina District': 15},
        'Marina District': {'Mission District': 20, 'Alamo Square': 15, 'Presidio': 10, 'Russian Hill': 8, 'North Beach': 11, 'Golden Gate Park': 18, 'Richmond District': 11, 'Embarcadero': 14, 'Financial District': 17, 'Marina District': 0}
    }
    
    # Friend data: name, location, available start and end times (in minutes from midnight), and desired duration
    friends = [
        {'name': 'Laura', 'location': 'Alamo Square', 'start': 14*60+30, 'end': 16*60+15, 'duration': 75},
        {'name': 'Brian', 'location': 'Presidio', 'start': 10*60+15, 'end': 17*60, 'duration': 30},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': 18*60, 'end': 20*60+15, 'duration': 90},
        {'name': 'Stephanie', 'location': 'North Beach', 'start': 10*60+15, 'end': 16*60, 'duration': 75},
        {'name': 'Helen', 'location': 'Golden Gate Park', 'start': 11*60+30, 'end': 21*60+45, 'duration': 120},
        {'name': 'Sandra', 'location': 'Richmond District', 'start': 8*60, 'end': 15*60+15, 'duration': 30},
        {'name': 'Mary', 'location': 'Embarcadero', 'start': 16*60+45, 'end': 18*60+45, 'duration': 120},
        {'name': 'Deborah', 'location': 'Financial District', 'start': 19*60, 'end': 20*60+45, 'duration': 105},
        {'name': 'Elizabeth', 'location': 'Marina District', 'start': 8*60+30, 'end': 13*60+15, 'duration': 105}
    ]
    
    start_time = 9*60  # 9:00 AM in minutes
    start_location = 'Mission District'
    
    best_schedule = []
    best_count = 0
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    def dfs(current_time, current_loc, met, schedule):
        nonlocal best_schedule, best_count
        if len(met) > best_count:
            best_count = len(met)
            best_schedule = schedule.copy()
        
        for friend in friends:
            if friend['name'] in met:
                continue
            t = travel_time[current_loc][friend['location']]
            arrival = current_time + t
            start_meeting = max(arrival, friend['start'])
            end_meeting = start_meeting + friend['duration']
            if end_meeting <= friend['end']:
                new_met = met | {friend['name']}
                new_schedule = schedule + [{
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_meeting),
                    'end_time': minutes_to_time(end_meeting)
                }]
                dfs(end_meeting, friend['location'], new_met, new_schedule)
    
    dfs(start_time, start_location, set(), [])
    
    result = {
        "itinerary": best_schedule
    }
    
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()