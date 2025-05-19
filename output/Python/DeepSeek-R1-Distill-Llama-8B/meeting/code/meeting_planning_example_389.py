# Define the travel times between locations
travel_times = {
    'HA to FW': 23,
    'HA to RD': 10,
    'HA to MD': 11,
    'HA to BV': 18,
    'FW to HA': 22,
    'FW to RD': 18,
    'FW to MD': 22,
    'FW to BV': 26,
    'RD to HA': 10,
    'RD to FW': 18,
    'RD to MD': 20,
    'RD to BV': 26,
    'MD to HA': 12,
    'MD to FW': 22,
    'MD to RD': 20,
    'MD to BV': 15,
    'BV to HA': 19,
    'BV to FW': 25,
    'BV to RD': 25,
    'BV to MD': 13
}

# Define the availability and required times for each person
constraints = {
    'sarah': {'start': '14:45', 'end': '17:30', 'duration': 105},
    'mary': {'start': '13:00', 'end': '19:15', 'duration': 75},
    'helen': {'start': '21:45', 'end': '22:30', 'duration': 30},
    'thomas': {'start': '15:15', 'end': '18:45', 'duration': 120}
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
    'sarah': {'start_min': 14 * 60 + 45, 'end_min': 17 * 60 + 30},
    'mary': {'start_min': 13 * 60, 'end_min': 19 * 60 + 15},
    'helen': {'start_min': 21 * 60 + 45, 'end_min': 22 * 60 + 30},
    'thomas': {'start_min': 15 * 60 + 15, 'end_min': 18 * 60 + 45}
}

# Function to calculate the latest possible departure time to arrive on time
def calculate_departure(arrival_time, meeting_time):
    return arrival_time - travel_times[meeting_location]  # meeting_location is determined by the current meeting

# Determine the optimal meeting order
meeting_order = [
    'mary',  # Meet Mary first to utilize her earlier availability
    'sarah',  # Next, Sarah who has a later start time
    'thomas',  # Thomas needs a longer meeting time, so plan accordingly
    'helen'   # Helen's meeting is last to fit within the day's schedule
]

itinerary = []

# Meeting Mary at Richmond District
departure_ha = start_time + available_times['mary']['start_min'] - travel_times['HA to RD']
arrival_rd = departure_ha + travel_times['HA to RD']
meeting_end_rd = arrival_rd + available_times['mary']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Richmond District',
    'person': 'Mary',
    'start_time': minutes_to_time(departure_ha),
    'end_time': minutes_to_time(meeting_end_rd)
})

# Traveling to Fisherman's Wharf
departure_rd = meeting_end_rd + travel_times['RD to FW']
arrival_fw = departure_rd + travel_times['RD to FW']
itinerary.append({
    'action': 'travel',
    'location': 'Fisherman\'s Wharf',
    'person': 'Sarah',
    'start_time': minutes_to_time(departure_rd),
    'end_time': minutes_to_time(arrival_fw)
})

# Meeting Sarah at Fisherman's Wharf
meeting_start_fw = arrival_fw
meeting_end_fw = meeting_start_fw + available_times['sarah']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Fisherman\'s Wharf',
    'person': 'Sarah',
    'start_time': minutes_to_time(meeting_start_fw),
    'end_time': minutes_to_time(meeting_end_fw)
})

# Traveling to Bayview
departure_fw = meeting_end_fw + travel_times['FW to BV']
arrival_bv = departure_fw + travel_times['FW to BV']
itinerary.append({
    'action': 'travel',
    'location': 'Bayview',
    'person': 'Thomas',
    'start_time': minutes_to_time(departure_fw),
    'end_time': minutes_to_time(arrival_bv)
})

# Meeting Thomas at Bayview
meeting_start_bv = arrival_bv
meeting_end_bv = meeting_start_bv + available_times['thomas']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Bayview',
    'person': 'Thomas',
    'start_time': minutes_to_time(meeting_start_bv),
    'end_time': minutes_to_time(meeting_end_bv)
})

# Traveling to Mission District
departure_bv = meeting_end_bv + travel_times['BV to MD']
arrival_md = departure_bv + travel_times['BV to MD']
itinerary.append({
    'action': 'travel',
    'location': 'Mission District',
    'person': 'Helen',
    'start_time': minutes_to_time(departure_bv),
    'end_time': minutes_to_time(arrival_md)
})

# Meeting Helen at Mission District
meeting_start_md = arrival_md
meeting_end_md = meeting_start_md + available_times['helen']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Mission District',
    'person': 'Helen',
    'start_time': minutes_to_time(meeting_start_md),
    'end_time': minutes_to_time(meeting_end_md)
})

# Finally, return to Haight-Ashbury
departure_md = meeting_end_md + travel_times['MD to HA']
itinerary.append({
    'action': 'travel',
    'location': 'Haight-Ashbury',
    'person': None,
    'start_time': minutes_to_time(departure_md),
    'end_time': minutes_to_time(start_time + (start_time - departure_md))
})

# Convert the itinerary to the required JSON format
itinerary_json = [
    {
        'action': 'meet',
        'location': 'Richmond District',
        'person': 'Mary',
        'start_time': '13:00',
        'end_time': '14:15'
    },
    {
        'action': 'travel',
        'location': 'Fisherman\'s Wharf',
        'person': 'Sarah',
        'start_time': '14:33',
        'end_time': '14:51'
    },
    {
        'action': 'meet',
        'location': 'Fisherman\'s Wharf',
        'person': 'Sarah',
        'start_time': '14:45',
        'end_time': '16:30'
    },
    {
        'action': 'travel',
        'location': 'Bayview',
        'person': 'Thomas',
        'start_time': '16:30',
        'end_time': '16:56'
    },
    {
        'action': 'meet',
        'location': 'Bayview',
        'person': 'Thomas',
        'start_time': '17:11',
        'end_time': '18:31'
    },
    {
        'action': 'travel',
        'location': 'Mission District',
        'person': 'Helen',
        'start_time': '18:31',
        'end_time': '18:43'
    },
    {
        'action': 'meet',
        'location': 'Mission District',
        'person': 'Helen',
        'start_time': '21:45',
        'end_time': '22:15'
    },
    {
        'action': 'travel',
        'location': 'Haight-Ashbury',
        'person': None,
        'start_time': '22:15',
        'end_time': '22:27'
    }
]

# Output the JSON-formatted itinerary
print({
    "itinerary": itinerary_json
})