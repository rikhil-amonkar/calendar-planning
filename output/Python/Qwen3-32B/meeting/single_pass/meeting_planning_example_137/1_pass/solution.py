import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Financial District': {
        'Chinatown': 5,
        'Golden Gate Park': 23
    },
    'Chinatown': {
        'Financial District': 5,
        'Golden Gate Park': 23
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Chinatown': 23
    }
}

friends = {
    'Barbara': {
        'location': 'Golden Gate Park',
        'available_start': 8 * 60 + 15,  # 495
        'available_end': 19 * 60,  # 1140 (7:00 PM)
        'min_duration': 45
    },
    'Kenneth': {
        'location': 'Chinatown',
        'available_start': 12 * 60,  # 720 (12:00 PM)
        'available_end': 15 * 60,  # 900 (3:00 PM)
        'min_duration': 90
    }
}

start_time_minutes = 9 * 60  # 540 (9:00 AM)

feasible_itineraries = []

def check_barbara_then_kenneth():
    current_time = start_time_minutes
    current_location = 'Financial District'
    itinerary = []
    
    # Travel to Barbara's location
    dest = friends['Barbara']['location']
    try:
        travel_time = travel_times[current_location][dest]
    except KeyError:
        return
    current_time += travel_time
    arrival = current_time
    
    # Schedule Barbara's meeting
    available_start = friends['Barbara']['available_start']
    available_end = friends['Barbara']['available_end']
    min_duration = friends['Barbara']['min_duration']
    
    meeting_start = max(arrival, available_start)
    meeting_end = meeting_start + min_duration
    
    if meeting_end > available_end:
        return
    
    # Add to itinerary
    itinerary.append({
        'action': 'meet',
        'location': dest,
        'person': 'Barbara',
        'start_time': minutes_to_time(meeting_start),
        'end_time': minutes_to_time(meeting_end)
    })
    current_location = dest
    current_time = meeting_end
    
    # Travel to Kenneth's location
    dest_k = friends['Kenneth']['location']
    try:
        travel_time_k = travel_times[current_location][dest_k]
    except KeyError:
        return
    current_time += travel_time_k
    arrival_k = current_time
    
    # Schedule Kenneth's meeting
    available_start_k = friends['Kenneth']['available_start']
    available_end_k = friends['Kenneth']['available_end']
    min_duration_k = friends['Kenneth']['min_duration']
    
    meeting_start_k = max(arrival_k, available_start_k)
    meeting_end_k = meeting_start_k + min_duration_k
    
    if meeting_end_k > available_end_k:
        return
    
    itinerary.append({
        'action': 'meet',
        'location': dest_k,
        'person': 'Kenneth',
        'start_time': minutes_to_time(meeting_start_k),
        'end_time': minutes_to_time(meeting_end_k)
    })
    
    feasible_itineraries.append(itinerary)

def check_kenneth_then_barbara():
    current_time = start_time_minutes
    current_location = 'Financial District'
    itinerary = []
    
    # Travel to Kenneth's location
    dest = friends['Kenneth']['location']
    try:
        travel_time = travel_times[current_location][dest]
    except KeyError:
        return
    current_time += travel_time
    arrival = current_time
    
    # Schedule Kenneth's meeting
    available_start = friends['Kenneth']['available_start']
    available_end = friends['Kenneth']['available_end']
    min_duration = friends['Kenneth']['min_duration']
    
    meeting_start = max(arrival, available_start)
    meeting_end = meeting_start + min_duration
    
    if meeting_end > available_end:
        return
    
    # Add to itinerary
    itinerary.append({
        'action': 'meet',
        'location': dest,
        'person': 'Kenneth',
        'start_time': minutes_to_time(meeting_start),
        'end_time': minutes_to_time(meeting_end)
    })
    current_location = dest
    current_time = meeting_end
    
    # Travel to Barbara's location
    dest_b = friends['Barbara']['location']
    try:
        travel_time_b = travel_times[current_location][dest_b]
    except KeyError:
        return
    current_time += travel_time_b
    arrival_b = current_time
    
    # Schedule Barbara's meeting
    available_start_b = friends['Barbara']['available_start']
    available_end_b = friends['Barbara']['available_end']
    min_duration_b = friends['Barbara']['min_duration']
    
    meeting_start_b = max(arrival_b, available_start_b)
    meeting_end_b = meeting_start_b + min_duration_b
    
    if meeting_end_b > available_end_b:
        return
    
    itinerary.append({
        'action': 'meet',
        'location': dest_b,
        'person': 'Barbara',
        'start_time': minutes_to_time(meeting_start_b),
        'end_time': minutes_to_time(meeting_end_b)
    })
    
    feasible_itineraries.append(itinerary)

# Run checks
check_barbara_then_kenneth()
check_kenneth_then_barbara()

# Find the best itinerary
best_itinerary = None
if feasible_itineraries:
    best_end_time = float('inf')
    for it in feasible_itineraries:
        last_meeting = it[-1]
        et_str = last_meeting['end_time']
        h, m = map(int, et_str.split(':'))
        end_minutes = h * 60 + m
        if end_minutes < best_end_time:
            best_end_time = end_minutes
            best_itinerary = it

# Output JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result))