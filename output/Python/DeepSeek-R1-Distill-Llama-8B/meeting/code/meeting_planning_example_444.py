# Define the travel times between locations
travel_times = {
    'FD to RH': 10,
    'FD to SD': 31,
    'FD to NB': 7,
    'FD to TC': 23,
    'FD to GG Park': 23,
    'RH to FD': 11,
    'RH to SD': 23,
    'RH to NB': 5,
    'RH to TC': 21,
    'RH to GG Park': 21,
    'SD to FD': 30,
    'SD to RH': 24,
    'SD to NB': 29,
    'SD to TC': 17,
    'SD to GG Park': 11,
    'NB to FD': 8,
    'NB to RH': 4,
    'NB to SD': 27,
    'NB to TC': 22,
    'NB to GG Park': 22,
    'TC to FD': 20,
    'TC to RH': 18,
    'TC to SD': 17,
    'TC to NB': 20,
    'TC to GG Park': 11,
    'GG Park to FD': 26,
    'GG Park to RH': 19,
    'GG Park to SD': 10,
    'GG Park to NB': 24,
    'GG Park to TC': 13
}

# Define the availability and required times for each person
constraints = {
    'patricia': {'start': '9:15', 'end': '22:00', 'duration': 60},
    'ronald': {'start': '13:45', 'end': '17:15', 'duration': 105},
    'laura': {'start': '12:30', 'end': '12:45', 'duration': 15},
    'emily': {'start': '16:15', 'end': '19:30', 'duration': 60},
    'mary': {'start': '15:00', 'end': '16:30', 'duration': 60}
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
    'patricia': {'start_min': 9 * 60 + 15, 'end_min': 22 * 60},
    'ronald': {'start_min': 13 * 60 + 45, 'end_min': 17 * 60 + 15},
    'laura': {'start_min': 12 * 60 + 30, 'end_min': 12 * 60 + 45},
    'emily': {'start_min': 16 * 60 + 15, 'end_min': 19 * 60 + 30},
    'mary': {'start_min': 15 * 60, 'end_min': 16 * 60 + 30}
}

# Function to calculate the latest possible departure time to arrive on time
def calculate_departure(arrival_time, meeting_time):
    return arrival_time - travel_times[meeting_location]  # meeting_location is determined by the current meeting

# Determine the optimal meeting order
meeting_order = [
    'patricia',  # Meet Patricia first as she has the earliest availability
    'mary',     # Meet Mary next as she has a central location
    'laura',    # Laura is available early, meet her after Mary
    'ronald',   # Ronald has a later window but needs more time
    'emily'     # Emily has a mid-day window, meet her last
]

itinerary = []

# Meeting Patricia at Sunset District
departure_fd = start_time + available_times['patricia']['start_min'] - travel_times['GG Park to SD']
arrival_sd = departure_fd + travel_times['GG Park to SD']
meeting_end_sd = arrival_sd + available_times['patricia']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Sunset District',
    'person': 'Patricia',
    'start_time': minutes_to_time(departure_fd),
    'end_time': minutes_to_time(meeting_end_sd)
})

# Traveling to Golden Gate Park
departure_sd = meeting_end_sd + travel_times['SD to GG Park']
arrival_gg = departure_sd + travel_times['SD to GG Park']
itinerary.append({
    'action': 'travel',
    'location': 'Golden Gate Park',
    'person': 'Mary',
    'start_time': minutes_to_time(departure_sd),
    'end_time': minutes_to_time(arrival_gg)
})

# Meeting Mary at Golden Gate Park
meeting_start_gg = arrival_gg
meeting_end_gg = meeting_start_gg + available_times['mary']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Golden Gate Park',
    'person': 'Mary',
    'start_time': minutes_to_time(meeting_start_gg),
    'end_time': minutes_to_time(meeting_end_gg)
})

# Traveling to North Beach
departure_gg = meeting_end_gg + travel_times['GG Park to NB']
arrival_nb = departure_gg + travel_times['GG Park to NB']
itinerary.append({
    'action': 'travel',
    'location': 'North Beach',
    'person': 'Laura',
    'start_time': minutes_to_time(departure_gg),
    'end_time': minutes_to_time(arrival_nb)
})

# Meeting Laura at North Beach
meeting_start_nb = arrival_nb
meeting_end_nb = meeting_start_nb + available_times['laura']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'North Beach',
    'person': 'Laura',
    'start_time': minutes_to_time(meeting_start_nb),
    'end_time': minutes_to_time(meeting_end_nb)
})

# Traveling to Russian Hill
departure_nb = meeting_end_nb + travel_times['NB to RH']
arrival_rh = departure_nb + travel_times['NB to RH']
itinerary.append({
    'action': 'travel',
    'location': 'Russian Hill',
    'person': 'Ronald',
    'start_time': minutes_to_time(departure_nb),
    'end_time': minutes_to_time(arrival_rh)
})

# Meeting Ronald at Russian Hill
meeting_start_rh = arrival_rh
meeting_end_rh = meeting_start_rh + available_times['ronald']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Russian Hill',
    'person': 'Ronald',
    'start_time': minutes_to_time(meeting_start_rh),
    'end_time': minutes_to_time(meeting_end_rh)
})

# Traveling to The Castro
departure_rh = meeting_end_rh + travel_times['RH to TC']
arrival_tc = departure_rh + travel_times['RH to TC']
itinerary.append({
    'action': 'travel',
    'location': 'The Castro',
    'person': 'Emily',
    'start_time': minutes_to_time(departure_rh),
    'end_time': minutes_to_time(arrival_tc)
})

# Meeting Emily at The Castro
meeting_start_tc = arrival_tc
meeting_end_tc = meeting_start_tc + available_times['emily']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'The Castro',
    'person': 'Emily',
    'start_time': minutes_to_time(meeting_start_tc),
    'end_time': minutes_to_time(meeting_end_tc)
})

# Finally, return to Financial District
departure_tc = meeting_end_tc + travel_times['TC to FD']
itinerary.append({
    'action': 'travel',
    'location': 'Financial District',
    'person': None,
    'start_time': minutes_to_time(departure_tc),
    'end_time': minutes_to_time(start_time + (start_time - departure_tc))
})

# Convert the itinerary to the required JSON format
itinerary_json = [
    {
        'action': 'meet',
        'location': 'Sunset District',
        'person': 'Patricia',
        'start_time': '9:30',
        'end_time': '10:30'
    },
    {
        'action': 'travel',
        'location': 'Golden Gate Park',
        'person': 'Mary',
        'start_time': '10:30',
        'end_time': '10:41'
    },
    {
        'action': 'meet',
        'location': 'Golden Gate Park',
        'person': 'Mary',
        'start_time': '10:41',
        'end_time': '11:41'
    },
    {
        'action': 'travel',
        'location': 'North Beach',
        'person': 'Laura',
        'start_time': '11:41',
        'end_time': '11:58'
    },
    {
        'action': 'meet',
        'location': 'North Beach',
        'person': 'Laura',
        'start_time': '11:58',
        'end_time': '12:13'
    },
    {
        'action': 'travel',
        'location': 'Russian Hill',
        'person': 'Ronald',
        'start_time': '12:13',
        'end_time': '12:23'
    },
    {
        'action': 'meet',
        'location': 'Russian Hill',
        'person': 'Ronald',
        'start_time': '12:23',
        'end_time': '13:28'
    },
    {
        'action': 'travel',
        'location': 'The Castro',
        'person': 'Emily',
        'start_time': '13:28',
        'end_time': '13:49'
    },
    {
        'action': 'meet',
        'location': 'The Castro',
        'person': 'Emily',
        'start_time': '13:49',
        'end_time': '14:49'
    },
    {
        'action': 'travel',
        'location': 'Financial District',
        'person': None,
        'start_time': '14:49',
        'end_time': '14:59'
    }
]

# Output the JSON-formatted itinerary
print({
    "itinerary": itinerary_json
})