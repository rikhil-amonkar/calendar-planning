from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16
}

itinerary = []

# Try meeting Kenneth first
kenneth_available_start = time(12, 0)
kenneth_available_end = time(15, 45)
kenneth_required_duration = 45

kenneth_latest_start = kenneth_available_end - timedelta(minutes=kenneth_required_duration)
kenneth_latest_start = time(15, 0) - timedelta(minutes=45)  # 3:00 PM

kenneth_earliest_start = kenneth_available_start  # 12:00 PM

kenneth_possible_start_times = []
for hour in range(kenneth_earliest_start.hour, kenneth_latest_start.hour + 1):
    for minute in range(0, 60, 15):
        start_time = time(hour, minute)
        kenneth_possible_start_times.append(start_time)

for kenneth_start in kenneth_possible_start_times:
    departure_kenneth = kenneth_start - timedelta(minutes=distance[('Nob Hill', 'Mission District')])
    if departure_kenneth < time(9, 0):
        continue
    arrival_kenneth = kenneth_start
    meeting_end_kenneth = arrival_kenneth + timedelta(minutes=kenneth_required_duration)
    if meeting_end_kenneth > kenneth_available_end:
        continue
    # Travel back to Nob Hill
    departure_back = arrival_kenneth + timedelta(minutes=distance[('Mission District', 'Nob Hill')])
    arrival_back = departure_back
    # Travel to Pacific Heights
    departure_pacific = arrival_back + timedelta(minutes=distance[('Nob Hill', 'Pacific Heights')])
    arrival_pacific = departure_pacific
    # Now, check Thomas
    earliest_thomas_start_possible = max(arrival_pacific, time(15, 30))
    if earliest_thomas_start_possible > time(18, 0):  # 6:40 PM
        continue
    # Thomas's latest start is 6:40 PM
    departure_thomas = time(18, 0) - timedelta(minutes=distance[('Nob Hill', 'Pacific Heights')])
    if departure_thomas < time(9, 0):
        continue
    arrival_thomas = departure_thomas
    meeting_end_thomas = arrival_thomas + timedelta(minutes=75)
    if meeting_end_thomas > time(19, 15):  # 7:15 PM
        continue
    # All times valid
    itinerary.append({
        'action': 'meet',
        'location': 'Mission District',
        'person': 'Kenneth',
        'start_time': kenneth_start.strftime("%H:%M"),
        'end_time': meeting_end_kenneth.strftime("%H:%M")
    })
    itinerary.append({
        'action': 'meet',
        'location': 'Pacific Heights',
        'person': 'Thomas',
        'start_time': departure_thomas.strftime("%H:%M"),
        'end_time': meeting_end_thomas.strftime("%H:%M")
    })
    break

if not itinerary:
    # Try meeting Thomas first
    thomas_available_start = time(15, 30)
    thomas_available_end = time(19, 15)
    thomas_required_duration = 75

    thomas_latest_start = thomas_available_end - timedelta(minutes=thomas_required_duration)
    thomas_latest_start = time(18, 0)  # 6:40 PM

    thomas_earliest_start = thomas_available_start  # 3:30 PM

    thomas_possible_start_times = []
    for hour in range(thomas_earliest_start.hour, thomas_latest_start.hour + 1):
        for minute in range(0, 60, 15):
            start_time = time(hour, minute)
            thomas_possible_start_times.append(start_time)

    for thomas_start in thomas_possible_start_times:
        departure_thomas = thomas_start - timedelta(minutes=distance[('Nob Hill', 'Pacific Heights')])
        if departure_thomas < time(9, 0):
            continue
        arrival_thomas = departure_thomas
        meeting_end_thomas = arrival_thomas + timedelta(minutes=thomas_required_duration)
        if meeting_end_thomas > thomas_available_end:
            continue
        # Travel back to Nob Hill
        departure_back = arrival_thomas + timedelta(minutes=distance[('Pacific Heights', 'Nob Hill')])
        arrival_back = departure_back
        # Travel to Mission District
        departure_kenneth = arrival_back + timedelta(minutes=distance[('Nob Hill', 'Mission District')])
        arrival_kenneth = departure_kenneth
        # Now, check Kenneth
        earliest_kenneth_start_possible = max(arrival_kenneth, time(12, 0))
        if earliest_kenneth_start_possible > time(15, 0):  # 3:00 PM
            continue
        # Kenneth's latest start is 3:00 PM
        departure_kenneth_final = time(15, 0) - timedelta(minutes=distance[('Nob Hill', 'Mission District')])
        if departure_kenneth_final < time(9, 0):
            continue
        arrival_kenneth_final = departure_kenneth_final
        meeting_end_kenneth_final = arrival_kenneth_final + timedelta(minutes=45)
        if meeting_end_kenneth_final > time(15, 45):  # 3:45 PM
            continue
        # All times valid
        itinerary.append({
            'action': 'meet',
            'location': 'Pacific Heights',
            'person': 'Thomas',
            'start_time': thomas_start.strftime("%H:%M"),
            'end_time': meeting_end_thomas.strftime("%H:%M")
        })
        itinerary.append({
            'action': 'meet',
            'location': 'Mission District',
            'person': 'Kenneth',
            'start_time': departure_kenneth_final.strftime("%H:%M"),
            'end_time': meeting_end_kenneth_final.strftime("%H:%M")
        })
        break

# Convert to JSON
itinerary_dict = {
    "itinerary": []
}
for item in itinerary:
    start = item['start_time']
    end = item['end_time']
    location = item['location']
    person = item['person']
    itinerary_dict["itinerary"].append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start,
        "end_time": end
    })

print(json.dumps(itinerary_dict))