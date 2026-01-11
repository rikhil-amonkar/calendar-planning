import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times matrix (in minutes)
    travel = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
    }

    # Friend data: location, window start, window end, min duration (minutes)
    friends = [
        {'name': 'Nancy', 'loc': 'Chinatown', 'start': '9:30', 'end': '13:30', 'dur': 90},
        {'name': 'Mary', 'loc': 'Alamo Square', 'start': '7:00', 'end': '21:00', 'dur': 75},
        {'name': 'Jessica', 'loc': 'Bayview', 'start': '11:15', 'end': '13:45', 'dur': 45},
        {'name': 'Rebecca', 'loc': 'Fisherman\'s Wharf', 'start': '7:00', 'end': '8:30', 'dur': 45},
    ]

    # Start at Financial District at 9:00
    current_time = time_to_minutes('9:00')
    current_loc = 'Financial District'
    itinerary = []

    # Order: Nancy -> Jessica -> Mary (pre-planned feasible order)
    plan = [
        ('Nancy', 'Chinatown', 90),
        ('Jessica', 'Bayview', 45),
        ('Mary', 'Alamo Square', 75),
    ]

    for person, loc, dur in plan:
        # Travel to loc
        travel_key = (current_loc, loc)
        travel_time = travel.get(travel_key, 0)
        arrival = current_time + travel_time

        # Find friend data
        friend = next(f for f in friends if f['name'] == person)
        window_start = time_to_minutes(friend['start'])
        window_end = time_to_minutes(friend['end'])

        # If we arrive before window start, wait
        if arrival < window_start:
            arrival = window_start

        # Check if we can meet for full duration before window ends
        if arrival + dur > window_end:
            # This shouldn't happen in our planned sequence
            print(f"Cannot meet {person} as planned.")
            break

        # Schedule meeting
        meeting_start = arrival
        meeting_end = arrival + dur

        itinerary.append({
            'action': 'meet',
            'location': loc,
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end),
        })

        # Update current time and location
        current_time = meeting_end
        current_loc = loc

    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()