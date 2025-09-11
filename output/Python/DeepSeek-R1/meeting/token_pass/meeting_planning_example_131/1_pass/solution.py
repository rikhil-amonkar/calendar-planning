import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    total_hours = 9 + minutes // 60
    total_minutes = minutes % 60
    return f"{total_hours}:{total_minutes:02d}"

def main():
    travel_times = {
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Marina District'): 6,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Marina District'): 10,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Presidio'): 10
    }
    
    jason_constraints = {
        'location': 'Presidio',
        'available_start': '10:00',
        'available_end': '16:15',
        'min_duration': 90
    }
    
    kenneth_constraints = {
        'location': 'Marina District',
        'available_start': '15:30',
        'available_end': '16:45',
        'min_duration': 45
    }
    
    jason_start_min = time_to_minutes(jason_constraints['available_start'])
    jason_end_min = time_to_minutes(jason_constraints['available_end'])
    kenneth_start_min = time_to_minutes(kenneth_constraints['available_start'])
    kenneth_end_min = time_to_minutes(kenneth_constraints['available_end'])
    
    travel_to_jason = travel_times[('Pacific Heights', 'Presidio')]
    travel_to_kenneth = travel_times[('Presidio', 'Marina District')]
    
    latest_departure_from_jason = kenneth_end_min - kenneth_constraints['min_duration'] - travel_to_kenneth
    jason_start = min(latest_departure_from_jason - jason_constraints['min_duration'], jason_end_min - jason_constraints['min_duration'])
    jason_start = max(jason_start, jason_start_min, travel_to_jason)
    
    jason_end = jason_start + jason_constraints['min_duration']
    arrival_at_kenneth = jason_end + travel_to_kenneth
    kenneth_start = max(arrival_at_kenneth, kenneth_start_min)
    kenneth_end = kenneth_start + kenneth_constraints['min_duration']
    
    if kenneth_end > kenneth_end_min or jason_end > jason_end_min:
        itinerary = []
    else:
        itinerary = [
            {
                "action": "meet",
                "location": jason_constraints['location'],
                "person": "Jason",
                "start_time": minutes_to_time(jason_start),
                "end_time": minutes_to_time(jason_end)
            },
            {
                "action": "meet",
                "location": kenneth_constraints['location'],
                "person": "Kenneth",
                "start_time": minutes_to_time(kenneth_start),
                "end_time": minutes_to_time(kenneth_end)
            }
        ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()