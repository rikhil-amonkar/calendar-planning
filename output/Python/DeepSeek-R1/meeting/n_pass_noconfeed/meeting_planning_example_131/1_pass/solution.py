import json

def format_minutes(minutes):
    hours = minutes // 60
    minutes_part = minutes % 60
    return f"{hours}:{minutes_part:02d}"

def main():
    travel_times = {
        'Pacific Heights': {'Presidio': 11, 'Marina District': 6},
        'Presidio': {'Pacific Heights': 11, 'Marina District': 10},
        'Marina District': {'Pacific Heights': 7, 'Presidio': 10}
    }
    
    jason = {
        'name': 'Jason',
        'location': 'Presidio',
        'available_start': 10 * 60,  # 10:00
        'available_end': 16 * 60 + 15,  # 16:15
        'min_duration': 90
    }
    
    kenneth = {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': 15 * 60 + 30,  # 15:30
        'available_end': 16 * 60 + 45,  # 16:45
        'min_duration': 45
    }
    
    orders = [
        [jason, kenneth],
        [kenneth, jason]
    ]
    
    start_time = 9 * 60  # 9:00 in minutes
    start_location = 'Pacific Heights'
    
    def try_order(order, start_time, start_location, travel_times):
        current_time = start_time
        current_location = start_location
        itinerary = []
        for meeting in order:
            travel_time = travel_times[current_location][meeting['location']]
            current_time += travel_time
            start_meeting = max(current_time, meeting['available_start'])
            end_meeting = start_meeting + meeting['min_duration']
            if end_meeting > meeting['available_end']:
                break
            itinerary.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['name'],
                'start_time': start_meeting,
                'end_time': end_meeting
            })
            current_time = end_meeting
            current_location = meeting['location']
        return itinerary, len(itinerary)
    
    best_itinerary = []
    best_count = 0
    for order in orders:
        itinerary, count = try_order(order, start_time, start_location, travel_times)
        if count > best_count:
            best_count = count
            best_itinerary = itinerary
    
    formatted_itinerary = []
    for meeting in best_itinerary:
        formatted_meeting = {
            'action': meeting['action'],
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': format_minutes(meeting['start_time']),
            'end_time': format_minutes(meeting['end_time'])
        }
        formatted_itinerary.append(formatted_meeting)
    
    result = {
        'itinerary': formatted_itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()