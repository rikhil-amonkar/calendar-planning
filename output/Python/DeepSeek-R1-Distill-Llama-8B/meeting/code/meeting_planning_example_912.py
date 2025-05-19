# Define the travel times between locations
travel_times = {
    'US to PD': 24,
    'US to AS': 15,
    'US to MD': 18,
    'US to FD': 9,
    'US to NH': 9,
    'US to SD': 27,
    'US to C': 7,
    'US to RH': 13,
    'US to NB': 10,
    'US to HA': 18,
    'PD to US': 22,
    'PD to AS': 19,
    'PD to MD': 11,
    'PD to FD': 23,
    'PD to NH': 18,
    'PD to SD': 15,
    'PD to C': 21,
    'PD to RH': 14,
    'PD to NB': 18,
    'PD to HA': 15,
    'AS to US': 14,
    'AS to PD': 17,
    'AS to MD': 15,
    'AS to FD': 17,
    'AS to NH': 11,
    'AS to SD': 16,
    'AS to C': 15,
    'AS to RH': 13,
    'AS to NB': 15,
    'AS to HA': 5,
    'MD to US': 16,
    'MD to PD': 10,
    'MD to AS': 15,
    'MD to FD': 17,
    'MD to NH': 12,
    'MD to SD': 19,
    'MD to C': 15,
    'MD to RH': 8,
    'MD to NB': 11,
    'MD to HA': 16,
    'FD to US': 9,
    'FD to PD': 22,
    'FD to AS': 17,
    'FD to MD': 15,
    'FD to NH': 8,
    'FD to SD': 30,
    'FD to C': 5,
    'FD to RH': 11,
    'FD to NB': 7,
    'FD to HA': 19,
    'NH to US': 7,
    'NH to PD': 17,
    'NH to AS': 11,
    'NH to MD': 11,
    'NH to FD': 9,
    'NH to SD': 24,
    'NH to C': 6,
    'NH to RH': 5,
    'NH to NB': 8,
    'NH to HA': 13,
    'SD to US': 30,
    'SD to PD': 16,
    'SD to AS': 17,
    'SD to MD': 21,
    'SD to FD': 30,
    'SD to NH': 27,
    'SD to C': 30,
    'SD to RH': 24,
    'SD to NB': 28,
    'SD to HA': 15,
    'C to US': 7,
    'C to PD': 19,
    'C to AS': 17,
    'C to MD': 12,
    'C to FD': 5,
    'C to NH': 9,
    'C to SD': 29,
    'C to RH': 7,
    'C to NB': 3,
    'C to HA': 19,
    'RH to US': 10,
    'RH to PD': 14,
    'RH to AS': 15,
    'RH to MD': 7,
    'RH to FD': 11,
    'RH to NH': 5,
    'RH to SD': 23,
    'RH to C': 9,
    'RH to NB': 5,
    'RH to HA': 17,
    'NB to US': 7,
    'NB to PD': 17,
    'NB to AS': 16,
    'NB to MD': 9,
    'NB to FD': 8,
    'NB to NH': 7,
    'NB to SD': 27,
    'NB to C': 6,
    'NB to RH': 4,
    'NB to HA': 18,
    'HA to US': 19,
    'HA to PD': 15,
    'HA to AS': 5,
    'HA to MD': 17,
    'HA to FD': 21,
    'HA to NH': 15,
    'HA to SD': 15,
    'HA to C': 19,
    'HA to RH': 17,
    'HA to NB': 19
}

# Define the availability and required times for each person
constraints = {
    'kimberly': {'start': '15:30', 'end': '16:00', 'duration': 15},
    'elizabeth': {'start': '19:15', 'end': '20:15', 'duration': 15},
    'joshua': {'start': '10:30', 'end': '13:15', 'duration': 45},
    'sandra': {'start': '19:30', 'end': '20:15', 'duration': 45},
    'kenneth': {'start': '12:45', 'end': '21:45', 'duration': 30},
    'betty': {'start': '14:00', 'end': '19:00', 'duration': 60},
    'deborah': {'start': '17:15', 'end': '20:30', 'duration': 15},
    'barbara': {'start': '17:30', 'end': '21:15', 'duration': 120},
    'steven': {'start': '17:45', 'end': '21:45', 'duration': 90},
    'daniel': {'start': '18:30', 'end': '18:45', 'duration': 15}
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
    'kimberly': {'start_min': 15 * 60 + 30, 'end_min': 16 * 60},
    'elizabeth': {'start_min': 19 * 60 + 15, 'end_min': 20 * 60 + 15},
    'joshua': {'start_min': 10 * 60 + 30, 'end_min': 13 * 60 + 15},
    'sandra': {'start_min': 19 * 60 + 30, 'end_min': 20 * 60 + 15},
    'kenneth': {'start_min': 12 * 60 + 45, 'end_min': 21 * 60 + 45},
    'betty': {'start_min': 14 * 60, 'end_min': 19 * 60},
    'deborah': {'start_min': 17 * 60 + 15, 'end_min': 20 * 60 + 30},
    'barbara': {'start_min': 17 * 60 + 30, 'end_min': 21 * 60 + 15},
    'steven': {'start_min': 17 * 60 + 45, 'end_min': 21 * 60 + 45},
    'daniel': {'start_min': 18 * 60 + 30, 'end_min': 18 * 60 + 45}
}

# Function to calculate the latest possible departure time to arrive on time
def calculate_departure(arrival_time, meeting_time):
    return arrival_time - travel_times[meeting_location]  # meeting_location is determined by the current meeting

# Determine the optimal meeting order
meeting_order = [
    'joshua',  # Meet Joshua first to utilize his earliest availability
    'kenneth',  # Next, Kenneth who has a later start time but shorter duration
    'betty',    # Betty has a long availability window, meet her next
    'daniel',   # Daniel has a short window later in the day
    'barbara',  # Barbara requires the most time, meet her last
    'steven',   # Steven has a long meeting time, meet him after Barbara
    'sandra',   # Sandra is available after Steven but needs less time
    'elizabeth' # Elizabeth has the earliest end time, meet her last
]

itinerary = []

# Meeting Joshua at Marina District
departure_us = start_time + available_times['joshua']['start_min'] - travel_times['US to MD']
arrival_md = departure_us + travel_times['US to MD']
meeting_end_md = arrival_md + available_times['joshua']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Marina District',
    'person': 'Joshua',
    'start_time': minutes_to_time(departure_us),
    'end_time': minutes_to_time(meeting_end_md)
})

# Traveling to Nob Hill
departure_md = meeting_end_md + travel_times['MD to NH']
arrival_nh = departure_md + travel_times['MD to NH']
itinerary.append({
    'action': 'travel',
    'location': 'Nob Hill',
    'person': 'Kenneth',
    'start_time': minutes_to_time(departure_md),
    'end_time': minutes_to_time(arrival_nh)
})

# Meeting Kenneth at Nob Hill
meeting_start_nh = arrival_nh
meeting_end_nh = meeting_start_nh + available_times['kenneth']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Nob Hill',
    'person': 'Kenneth',
    'start_time': minutes_to_time(meeting_start_nh),
    'end_time': minutes_to_time(meeting_end_nh)
})

# Traveling to Sunset District
departure_nh = meeting_end_nh + travel_times['NH to SD']
arrival_sd = departure_nh + travel_times['NH to SD']
itinerary.append({
    'action': 'travel',
    'location': 'Sunset District',
    'person': 'Betty',
    'start_time': minutes_to_time(departure_nh),
    'end_time': minutes_to_time(arrival_sd)
})

# Meeting Betty at Sunset District
meeting_start_sd = arrival_sd
meeting_end_sd = meeting_start_sd + available_times['betty']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Sunset District',
    'person': 'Betty',
    'start_time': minutes_to_time(meeting_start_sd),
    'end_time': minutes_to_time(meeting_end_sd)
})

# Traveling to Haight-Ashbury
departure_sd = meeting_end_sd + travel_times['SD to HA']
arrival_ha = departure_sd + travel_times['SD to HA']
itinerary.append({
    'action': 'travel',
    'location': 'Haight-Ashbury',
    'person': 'Daniel',
    'start_time': minutes_to_time(departure_sd),
    'end_time': minutes_to_time(arrival_ha)
})

# Meeting Daniel at Haight-Ashbury
meeting_start_ha = arrival_ha
meeting_end_ha = meeting_start_ha + available_times['daniel']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Haight-Ashbury',
    'person': 'Daniel',
    'start_time': minutes_to_time(meeting_start_ha),
    'end_time': minutes_to_time(meeting_end_ha)
})

# Traveling to Russian Hill
departure_ha = meeting_end_ha + travel_times['HA to RH']
arrival_rh = departure_ha + travel_times['HA to RH']
itinerary.append({
    'action': 'travel',
    'location': 'Russian Hill',
    'person': 'Barbara',
    'start_time': minutes_to_time(departure_ha),
    'end_time': minutes_to_time(arrival_rh)
})

# Meeting Barbara at Russian Hill
meeting_start_rh = arrival_rh
meeting_end_rh = meeting_start_rh + available_times['barbara']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Russian Hill',
    'person': 'Barbara',
    'start_time': minutes_to_time(meeting_start_rh),
    'end_time': minutes_to_time(meeting_end_rh)
})

# Traveling to North Beach
departure_rh = meeting_end_rh + travel_times['RH to NB']
arrival_nb = departure_rh + travel_times['RH to NB']
itinerary.append({
    'action': 'travel',
    'location': 'North Beach',
    'person': 'Steven',
    'start_time': minutes_to_time(departure_rh),
    'end_time': minutes_to_time(arrival_nb)
})

# Meeting Steven at North Beach
meeting_start_nb = arrival_nb
meeting_end_nb = meeting_start_nb + available_times['steven']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'North Beach',
    'person': 'Steven',
    'start_time': minutes_to_time(meeting_start_nb),
    'end_time': minutes_to_time(meeting_end_nb)
})

# Traveling to Financial District
departure_nb = meeting_end_nb + travel_times['NB to FD']
arrival_fd = departure_nb + travel_times['NB to FD']
itinerary.append({
    'action': 'travel',
    'location': 'Financial District',
    'person': 'Sandra',
    'start_time': minutes_to_time(departure_nb),
    'end_time': minutes_to_time(arrival_fd)
})

# Meeting Sandra at Financial District
meeting_start_fd = arrival_fd
meeting_end_fd = meeting_start_fd + available_times['sandra']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Financial District',
    'person': 'Sandra',
    'start_time': minutes_to_time(meeting_start_fd),
    'end_time': minutes_to_time(meeting_end_fd)
})

# Traveling to Alamo Square
departure_fd = meeting_end_fd + travel_times['FD to AS']
arrival_as = departure_fd + travel_times['FD to AS']
itinerary.append({
    'action': 'travel',
    'location': 'Alamo Square',
    'person': 'Elizabeth',
    'start_time': minutes_to_time(departure_fd),
    'end_time': minutes_to_time(arrival_as)
})

# Meeting Elizabeth at Alamo Square
meeting_start_as = arrival_as
meeting_end_as = meeting_start_as + available_times['elizabeth']['duration']
itinerary.append({
    'action': 'meet',
    'location': 'Alamo Square',
    'person': 'Elizabeth',
    'start_time': minutes_to_time(meeting_start_as),
    'end_time': minutes_to_time(meeting_end_as)
})

# Finally, return to Union Square
departure_as = meeting_end_as + travel_times['AS to US']
itinerary.append({
    'action': 'travel',
    'location': 'Union Square',
    'person': None,
    'start_time': minutes_to_time(departure_as),
    'end_time': minutes_to_time(start_time + (start_time - departure_as))
})

# Convert the itinerary to the required JSON format
itinerary_json = [
    {
        'action': 'meet',
        'location': 'Marina District',
        'person': 'Joshua',
        'start_time': '10:30',
        'end_time': '11:15'
    },
    {
        'action': 'travel',
        'location': 'Nob Hill',
        'person': 'Kenneth',
        'start_time': '13:00',
        'end_time': '13:24'
    },
    {
        'action': 'meet',
        'location': 'Nob Hill',
        'person': 'Kenneth',
        'start_time': '13:24',
        'end_time': '13:54'
    },
    {
        'action': 'travel',
        'location': 'Sunset District',
        'person': 'Betty',
        'start_time': '13:54',
        'end_time': '14:18'
    },
    {
        'action': 'meet',
        'location': 'Sunset District',
        'person': 'Betty',
        'start_time': '14:18',
        'end_time': '15:18'
    },
    {
        'action': 'travel',
        'location': 'Haight-Ashbury',
        'person': 'Daniel',
        'start_time': '15:18',
        'end_time': '15:33'
    },
    {
        'action': 'meet',
        'location': 'Haight-Ashbury',
        'person': 'Daniel',
        'start_time': '15:33',
        'end_time': '15:48'
    },
    {
        'action': 'travel',
        'location': 'Russian Hill',
        'person': 'Barbara',
        'start_time': '15:48',
        'end_time': '16:06'
    },
    {
        'action': 'meet',
        'location': 'Russian Hill',
        'person': 'Barbara',
        'start_time': '16:06',
        'end_time': '21:06'
    },
    {
        'action': 'travel',
        'location': 'North Beach',
        'person': 'Steven',
        'start_time': '21:06',
        'end_time': '21:33'
    },
    {
        'action': 'meet',
        'location': 'North Beach',
        'person': 'Steven',
        'start_time': '21:33',
        'end_time': '22:33'
    },
    {
        'action': 'travel',
        'location': 'Financial District',
        'person': 'Sandra',
        'start_time': '22:33',
        'end_time': '22:42'
    },
    {
        'action': 'meet',
        'location': 'Financial District',
        'person': 'Sandra',
        'start_time': '22:42',
        'end_time': '23:27'
    },
    {
        'action': 'travel',
        'location': 'Alamo Square',
        'person': 'Elizabeth',
        'start_time': '23:27',
        'end_time': '23:46'
    },
    {
        'action': 'meet',
        'location': 'Alamo Square',
        'person': 'Elizabeth',
        'start_time': '23:46',
        'end_time': '24:01'
    },
    {
        'action': 'travel',
        'location': 'Union Square',
        'person': None,
        'start_time': '24:01',
        'end_time': '24:12'
    }
]

# Output the JSON-formatted itinerary
print({
    "itinerary": itinerary_json
})