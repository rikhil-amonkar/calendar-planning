from datetime import time, timedelta

# Define travel distances between locations
distance = {
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Nob Hill'): 16,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Nob Hill'): 27,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Haight-Ashbury'): 13,
}

itinerary = []

# Try to meet as many friends as possible starting from Russian Hill at 9:00 AM
current_time = time(9, 0)

# Meeting Karen first
karen_start = time(9, 30)
karen_end = karen_start + timedelta(minutes=90)
if karen_end > time(12, 45):
    karen_end = time(12, 45)

# Calculate travel time from Russian Hill to Financial District
travel_time = distance[('Russian Hill', 'Financial District')]
arrival_time = karen_start + timedelta(minutes=travel_time)
if arrival_time < karen_start:
    arrival_time = karen_start

itinerary.append({
    'action': 'meet',
    'location': 'Financial District',
    'person': 'Karen',
    'start_time': karen_start.strftime("%H:%M"),
    'end_time': karen_end.strftime("%H:%M")
})

current_time = karen_end

# Meeting Kevin next
kevin_start = time(10, 0)
kevin_end = kevin_start + timedelta(minutes=120)
if kevin_end > time(5, 45):
    kevin_end = time(5, 45)

# Calculate travel time from Financial District to Sunset District
travel_time = distance[('Financial District', 'Sunset District')]
arrival_time = kevin_start + timedelta(minutes=travel_time)
if arrival_time < kevin_start:
    arrival_time = kevin_start

itinerary.append({
    'action': 'meet',
    'location': 'Sunset District',
    'person': 'Kevin',
    'start_time': kevin_start.strftime("%H:%M"),
    'end_time': kevin_end.strftime("%H:%M")
})

current_time = kevin_end

# Meeting Barbara next
barbara_start = time(12, 0)
barbara_end = barbara_start + timedelta(minutes=90)
if barbara_end > time(7, 30):
    barbara_end = time(7, 30)

# Calculate travel time from Sunset District to Alamo Square
travel_time = distance[('Sunset District', 'Alamo Square')]
arrival_time = barbara_start + timedelta(minutes=travel_time)
if arrival_time < barbara_start:
    arrival_time = barbara_start

itinerary.append({
    'action': 'meet',
    'location': 'Alamo Square',
    'person': 'Barbara',
    'start_time': barbara_start.strftime("%H:%M"),
    'end_time': barbara_end.strftime("%H:%M")
})

current_time = barbara_end

# Meeting Nancy next
nancy_start = time(14, 0)
nancy_end = nancy_start + timedelta(minutes=105)
if nancy_end > time(8, 0):
    nancy_end = time(8, 0)

# Calculate travel time from Alamo Square to Golden Gate Park
travel_time = distance[('Alamo Square', 'Golden Gate Park')]
arrival_time = nancy_start + timedelta(minutes=travel_time)
if arrival_time < nancy_start:
    arrival_time = nancy_start

itinerary.append({
    'action': 'meet',
    'location': 'Golden Gate Park',
    'person': 'Nancy',
    'start_time': nancy_start.strftime("%H:%M"),
    'end_time': nancy_end.strftime("%H:%M")
})

current_time = nancy_end

# Meeting David next
david_start = time(16, 0)
david_end = david_start + timedelta(minutes=120)
if david_end > time(19, 0):
    david_end = time(19, 0)

# Calculate travel time from Golden Gate Park to The Castro
travel_time = distance[('Golden Gate Park', 'The Castro')]
arrival_time = david_start + timedelta(minutes=travel_time)
if arrival_time < david_start:
    arrival_time = david_start

itinerary.append({
    'action': 'meet',
    'location': 'The Castro',
    'person': 'David',
    'start_time': david_start.strftime("%H:%M"),
    'end_time': david_end.strftime("%H:%M")
})

current_time = david_end

# Meeting Linda next
linda_start = time(18, 0)
linda_end = linda_start + timedelta(minutes=45)
if linda_end > time(19, 0):
    linda_end = time(19, 0)

# Calculate travel time from The Castro to Bayview
travel_time = distance[('The Castro', 'Bayview')]
arrival_time = linda_start + timedelta(minutes=travel_time)
if arrival_time < linda_start:
    arrival_time = linda_start

itinerary.append({
    'action': 'meet',
    'location': 'Bayview',
    'person': 'Linda',
    'start_time': linda_start.strftime("%H:%M"),
    'end_time': linda_end.strftime("%H:%M")
})

current_time = linda_end

# Meeting Mark last
mark_start = time(19, 0)
mark_end = mark_start + timedelta(minutes=90)
if mark_end > time(21, 0):
    mark_end = time(21, 0)

# Calculate travel time from Bayview to Marina District
travel_time = distance[('Bayview', 'Marina District')]
arrival_time = mark_start + timedelta(minutes=travel_time)
if arrival_time < mark_start:
    arrival_time = mark_start

itinerary.append({
    'action': 'meet',
    'location': 'Marina District',
    'person': 'Mark',
    'start_time': mark_start.strftime("%H:%M"),
    'end_time': mark_end.strftime("%H:%M")
})

current_time = mark_end

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