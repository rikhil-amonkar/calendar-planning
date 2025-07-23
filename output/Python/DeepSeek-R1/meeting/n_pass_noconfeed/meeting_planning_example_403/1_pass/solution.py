import json

def main():
    travel_times = {
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'The Castro'): 19,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'The Castro'): 16,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'The Castro'): 21,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'The Castro'): 22,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Chinatown'): 20
    }
    
    friends_in_order = [
        {'name': 'Robert', 'location': 'The Castro', 'start': 0, 'end': 315, 'duration': 30},
        {'name': 'Rebecca', 'location': 'Chinatown', 'start': 45, 'end': 750, 'duration': 90},
        {'name': 'Andrew', 'location': 'Golden Gate Park', 'start': 165, 'end': 330, 'duration': 75},
        {'name': 'Sarah', 'location': 'Pacific Heights', 'start': 435, 'end': 585, 'duration': 15},
        {'name': 'Nancy', 'location': 'Presidio', 'start': 510, 'end': 615, 'duration': 60}
    ]
    
    current_location = 'Union Square'
    current_time = 0
    itinerary = []
    
    def format_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"
    
    for friend in friends_in_order:
        travel_key = (current_location, friend['location'])
        travel_duration = travel_times.get(travel_key)
        if travel_duration is None:
            travel_key = (friend['location'], current_location)
            travel_duration = travel_times.get(travel_key)
            if travel_duration is None:
                continue
        arrival_time = current_time + travel_duration
        if arrival_time < friend['start']:
            start_meeting = friend['start']
        else:
            start_meeting = arrival_time
        end_meeting = start_meeting + friend['duration']
        if end_meeting > friend['end']:
            continue
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": format_time(start_meeting),
            "end_time": format_time(end_meeting)
        })
        current_time = end_meeting
        current_location = friend['location']
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()