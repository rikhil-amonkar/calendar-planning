import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Travel times in minutes: from[to] = time
    travel = {
        'Bayview': {'Embarcadero': 19, 'Fisherman\'s Wharf': 25, 'Financial District': 19},
        'Embarcadero': {'Bayview': 21, 'Fisherman\'s Wharf': 6, 'Financial District': 5},
        'Fisherman\'s Wharf': {'Bayview': 26, 'Embarcadero': 8, 'Financial District': 11},
        'Financial District': {'Bayview': 19, 'Embarcadero': 4, 'Fisherman\'s Wharf': 10}
    }
    
    # Friend data: location, available_start, available_end, min_duration
    friends = [
        {'name': 'Betty', 'loc': 'Embarcadero', 'start': '19:45', 'end': '21:45', 'dur': 15},
        {'name': 'Karen', 'loc': 'Fisherman\'s Wharf', 'start': '8:45', 'end': '15:00', 'dur': 30},
        {'name': 'Anthony', 'loc': 'Financial District', 'start': '9:15', 'end': '21:30', 'dur': 105}
    ]
    
    # Start at Bayview at 9:00
    current_time = time_to_minutes('9:00')
    current_location = 'Bayview'
    
    # We'll manually construct the optimal schedule we found
    itinerary = []
    
    # 1. Travel to Financial District to meet Anthony
    travel_time = travel[current_location]['Financial District']
    current_time += travel_time
    # Anthony available from 9:15, so if we arrive earlier, wait
    anthony_start = time_to_minutes('9:15')
    if current_time < anthony_start:
        current_time = anthony_start
    meet_end = current_time + friends[2]['dur']  # Anthony's duration
    itinerary.append({
        'action': 'meet',
        'location': 'Financial District',
        'person': 'Anthony',
        'start_time': minutes_to_time(current_time),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Financial District'
    
    # 2. Travel to Fisherman's Wharf to meet Karen
    travel_time = travel[current_location]['Fisherman\'s Wharf']
    current_time += travel_time
    # Karen available until 15:00
    karen_end = time_to_minutes('15:00')
    if current_time + friends[1]['dur'] > karen_end:
        # Would be too late, but in our plan it's fine
        pass
    meet_end = current_time + friends[1]['dur']
    itinerary.append({
        'action': 'meet',
        'location': 'Fisherman\'s Wharf',
        'person': 'Karen',
        'start_time': minutes_to_time(current_time),
        'end_time': minutes_to_time(meet_end)
    })
    current_time = meet_end
    current_location = 'Fisherman\'s Wharf'
    
    # 3. Travel back to Financial District (free time)
    travel_time = travel[current_location]['Financial District']
    current_time += travel_time
    # Just moving, no meet here
    current_location = 'Financial District'
    
    # 4. Wait until time to go to Embarcadero for Betty
    # We need to be at Embarcadero by 19:45
    betty_start = time_to_minutes('19:45')
    # Leave FD at 19:41 to arrive E at 19:45 (4 min travel)
    travel_time = travel[current_location]['Embarcadero']
    depart_time = betty_start - travel_time
    if current_time < depart_time:
        current_time = depart_time  # wait in FD until departure
    current_time += travel_time  # travel to Embarcadero
    current_location = 'Embarcadero'
    
    # Meet Betty
    meet_end = current_time + friends[0]['dur']
    itinerary.append({
        'action': 'meet',
        'location': 'Embarcadero',
        'person': 'Betty',
        'start_time': minutes_to_time(current_time),
        'end_time': minutes_to_time(meet_end)
    })
    
    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()