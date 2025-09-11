import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def plan_itinerary():
    # Define travel times
    travel_times = {
        ('FD', 'CT'): 5,
        ('FD', 'GGP'): 23,
        ('CT', 'FD'): 5,
        ('CT', 'GGP'): 23,
        ('GGP', 'FD'): 26,
        ('GGP', 'CT'): 23,
    }

    # Define friends' constraints
    friends = {
        'Barbara': {
            'location': 'GGP',
            'available_start': 8*60 + 15,  # 495
            'available_end': 19*60,         # 1140
            'min_duration': 45
        },
        'Kenneth': {
            'location': 'CT',
            'available_start': 12*60,       # 720
            'available_end': 15*60,         # 900
            'min_duration': 90
        }
    }

    # Starting conditions
    start_time = 9 * 60  # 540
    start_location = 'FD'

    # Possible itineraries
    itineraries = []

    # Option 1: Barbara first, then Kenneth
    current_time = start_time
    current_location = start_location
    itinerary = []

    # Travel to Barbara's location
    dest = friends['Barbara']['location']
    travel_time = travel_times.get((current_location, dest), 0)
    current_time += travel_time
    current_location = dest

    # Check if arrival is before Barbara's available start
    if current_time < friends['Barbara']['available_start']:
        meeting_start = friends['Barbara']['available_start']
    else:
        meeting_start = current_time

    # Calculate latest end time for Barbara's meeting to allow meeting Kenneth
    latest_end_barbara = friends['Kenneth']['available_start'] - travel_times.get((dest, friends['Kenneth']['location']), 0)
    if latest_end_barbara < meeting_start + friends['Barbara']['min_duration']:
        # Not enough time
        pass
    else:
        # Schedule Barbara's meeting with minimum duration
        meeting_end = meeting_start + friends['Barbara']['min_duration']
        if meeting_end > latest_end_barbara:
            # Adjust to latest_end_barbara, check duration
            duration = latest_end_barbara - meeting_start
            if duration < friends['Barbara']['min_duration']:
                pass
            else:
                meeting_end = latest_end_barbara
        itinerary.append({
            'action': 'meet',
            'location': dest,
            'person': 'Barbara',
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        # Update current_time and current_location
        current_time = meeting_end
        current_location = dest

        # Now, travel to Kenneth's location
        dest_kenneth = friends['Kenneth']['location']
        travel_time = travel_times.get((current_location, dest_kenneth), 0)
        current_time += travel_time
        current_location = dest_kenneth

        # Schedule Kenneth's meeting
        meeting_start_kenneth = max(current_time, friends['Kenneth']['available_start'])
        meeting_end_kenneth = meeting_start_kenneth + friends['Kenneth']['min_duration']
        if meeting_end_kenneth <= friends['Kenneth']['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': dest_kenneth,
                'person': 'Kenneth',
                'start_time': minutes_to_time(meeting_start_kenneth),
                'end_time': minutes_to_time(meeting_end_kenneth)
            })
            itineraries.append(itinerary)

    # Option 2: Kenneth first, then Barbara
    current_time = start_time
    current_location = start_location
    itinerary2 = []

    # Travel to Kenneth's location
    dest = friends['Kenneth']['location']
    travel_time = travel_times.get((current_location, dest), 0)
    current_time += travel_time
    current_location = dest

    # Schedule Kenneth's meeting
    meeting_start_kenneth = max(current_time, friends['Kenneth']['available_start'])
    meeting_end_kenneth = meeting_start_kenneth + friends['Kenneth']['min_duration']
    if meeting_end_kenneth <= friends['Kenneth']['available_end']:
        itinerary2.append({
            'action': 'meet',
            'location': dest,
            'person': 'Kenneth',
            'start_time': minutes_to_time(meeting_start_kenneth),
            'end_time': minutes_to_time(meeting_end_kenneth)
        })
        current_time = meeting_end_kenneth
        current_location = dest

        # Now, travel to Barbara's location
        dest_barbara = friends['Barbara']['location']
        travel_time = travel_times.get((current_location, dest_barbara), 0)
        current_time += travel_time
        current_location = dest_barbara

        # Schedule Barbara's meeting
        meeting_start_barbara = max(current_time, friends['Barbara']['available_start'])
        meeting_end_barbara = meeting_start_barbara + friends['Barbara']['min_duration']
        if meeting_end_barbara <= friends['Barbara']['available_end']:
            itinerary2.append({
                'action': 'meet',
                'location': dest_barbara,
                'person': 'Barbara',
                'start_time': minutes_to_time(meeting_start_barbara),
                'end_time': minutes_to_time(meeting_end_barbara)
            })
            itineraries.append(itinerary2)

    # Select the best itinerary (most meetings)
    if not itineraries:
        return []
    best_itinerary = max(itineraries, key=lambda x: len(x))
    return best_itinerary

# Generate the result
itinerary = plan_itinerary()

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))