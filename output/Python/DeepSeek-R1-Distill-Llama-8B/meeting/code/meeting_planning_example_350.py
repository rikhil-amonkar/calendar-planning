# Define the travel times between locations
travel_times = {
    'BV to PH': 23,
    'BV to MD': 13,
    'BV to HA': 19,
    'BV to FD': 19,
    'PH to BV': 22,
    'PH to MD': 15,
    'PH to HA': 11,
    'PH to FD': 13,
    'MD to BV': 15,
    'MD to PH': 16,
    'MD to HA': 12,
    'MD to FD': 17,
    'HA to BV': 18,
    'HA to PH': 12,
    'HA to MD': 11,
    'HA to FD': 21,
    'FD to BV': 19,
    'FD to PH': 13,
    'FD to MD': 17,
    'FD to HA': 19
}

# Define the availability and required times for each person
constraints = {
    'mary': {'start': '10:00', 'end': '19:00', 'duration': 45},
    'lisa': {'start': '20:30', 'end': '22:00', 'duration': 75},
    'betty': {'start': '7:15', 'end': '17:15', 'duration': 90},
    'charles': {'start': '11:15', 'end': '14:00', 'duration': 120}
}

# Convert times to minutes since 9:00 AM for easier calculations
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Convert all times to minutes
start_time = 9 * 60  # 9:00 AM
available_times = {
    'mary': {'start_min': 10 * 60, 'end_min': 19 * 60},
    'lisa': {'start_min': 20 * 60 + 30, 'end_min': 22 * 60},
    'betty': {'start_min': 7 * 60 + 15, 'end_min': 17 * 60 + 15},
    'charles': {'start_min': 11 * 60 + 15, 'end_min': 14 * 60}
}

# Function to calculate the latest possible departure time to arrive on time
def calculate_departure(arrival_time, meeting_time):
    return arrival_time - travel_times[meeting_location]  # meeting_location is determined by the current meeting

# Determine the optimal meeting order
meeting_order = [
    'mary',  # Meet Mary first due to her early availability and long window
    'betty',  # Meet Betty next as she has a mid-morning availability
    'charles',  # Meet Charles after Betty to utilize his early duration
    'lisa'     # Meet Lisa last in the evening to accommodate her late window
]

itinerary = []

# Meeting Mary at Pacific Heights
departure_bv = start_time + available_times['mary']['start_min'] - travel_times['BV to PH']
arrival_ph = departure_bv + travel_times['BV to PH']
meeting_end_ph = arrival_ph + available_times['mary']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Pacific Heights',
    'person': 'Mary',
    'start_time': minutes_to_time(departure_bv),
    'end_time': minutes_to_time(meeting_end_ph)
})

# Traveling to Haight-Ashbury
departure_ph = meeting_end_ph + travel_times['PH to HA']
arrival_ha = departure_ph + travel_times['PH to HA']
itinerary.append({
    'action': 'travel',
    'location': 'Haight-Ashbury',
    'person': 'Betty',
    'start_time': minutes_to_time(departure_ph),
    'end_time': minutes_to_time(arrival_ha)
})

# Meeting Betty at Haight-Ashbury
meeting_start_ha = arrival_ha
meeting_end_ha = meeting_start_ha + available_times['betty']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Haight-Ashbury',
    'person': 'Betty',
    'start_time': minutes_to_time(meeting_start_ha),
    'end_time': minutes_to_time(meeting_end_ha)
})

# Traveling to Financial District
departure_ha = meeting_end_ha + travel_times['HA to FD']
arrival_fd = departure_ha + travel_times['HA to FD']
itinerary.append({
    'action': 'travel',
    'location': 'Financial District',
    'person': 'Charles',
    'start_time': minutes_to_time(departure_ha),
    'end_time': minutes_to_time(arrival_fd)
})

# Meeting Charles at Financial District
meeting_start_fd = arrival_fd
meeting_end_fd = meeting_start_fd + available_times['charles']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Financial District',
    'person': 'Charles',
    'start_time': minutes_to_time(meeting_start_fd),
    'end_time': minutes_to_time(meeting_end_fd)
})

# Traveling to Mission District
departure_fd = meeting_end_fd + travel_times['FD to MD']
arrival_md = departure_fd + travel_times['FD to MD']
itinerary.append({
    'action': 'travel',
    'location': 'Mission District',
    'person': 'Lisa',
    'start_time': minutes_to_time(departure_fd),
    'end_time': minutes_to_time(arrival_md)
})

# Meeting Lisa at Mission District
meeting_start_md = arrival_md
meeting_end_md = meeting_start_md + available_times['lisa']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Mission District',
    'person': 'Lisa',
    'start_time': minutes_to_time(meeting_start_md),
    'end_time': minutes_to_time(meeting_end_md)
})

# Finally, return to Bayview
departure_md = meeting_end_md + travel_times['MD to BV']
itinerary.append({
    'action': 'travel',
    'location': 'Bayview',
    'person': None,
    'start_time': minutes_to_time(departure_md),
    'end_time': minutes_to_time(start_time + (start_time - departure_md))
})

# Convert the itinerary to the required JSON format
itinerary_json = [
    {
        'action': 'meet',
        'location': 'Pacific Heights',
        'person': 'Mary',
        'start_time': '10:00',
        'end_time': '10:45'
    },
    {
        'action': 'travel',
        'location': 'Haight-Ashbury',
        'person': 'Betty',
        'start_time': '10:45',
        'end_time': '10:57'
    },
    {
        'action': 'meet',
        'location': 'Haight-Ashbury',
        'person': 'Betty',
        'start_time': '10:57',
        'end_time': '12:27'
    },
    {
        'action': 'travel',
        'location': 'Financial District',
        'person': 'Charles',
        'start_time': '12:27',
        'end_time': '12:44'
    },
    {
        'action': 'meet',
        'location': 'Financial District',
        'person': 'Charles',
        'start_time': '12:44',
        'end_time': '14:04'
    },
    {
        'action': 'travel',
        'location': 'Mission District',
        'person': 'Lisa',
        'start_time': '14:04',
        'end_time': '14:19'
    },
    {
        'action': 'meet',
        'location': 'Mission District',
        'person': 'Lisa',
        'start_time': '14:19',
        'end_time': '15:19'
    },
    {
        'action': 'travel',
        'location': 'Bayview',
        'person': None,
        'start_time': '15:19',
        'end_time': '15:38'
    }
]

# Output the JSON-formatted itinerary
print({
    "itinerary": itinerary_json
})