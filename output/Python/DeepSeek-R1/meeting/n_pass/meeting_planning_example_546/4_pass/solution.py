import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define original travel times dictionary
original_travel_times = {
    'Embarcadero': {'Richmond District': 21, 'Union Square': 10, 'Financial District': 5, 'Pacific Heights': 11, 'Nob Hill': 10, 'Bayview': 21},
    'Richmond District': {'Embarcadero': 19, 'Union Square': 21, 'Financial District': 22, 'Pacific Heights': 10, 'Nob Hill': 17, 'Bayview': 26},
    'Union Square': {'Embarcadero': 11, 'Richmond District': 20, 'Financial District': 9, 'Pacific Heights': 15, 'Nob Hill': 9, 'Bayview': 15},
    'Financial District': {'Embarcadero': 4, 'Richmond District': 21, 'Union Square': 9, 'Pacific Heights': 13, 'Nob Hill': 8, 'Bayview': 19},
    'Pacific Heights': {'Embarcadero': 10, 'Richmond District': 12, 'Union Square': 12, 'Financial District': 13, 'Nob Hill': 8, 'Bayview': 22},
    'Nob Hill': {'Embarcadero': 9, 'Richmond District': 14, 'Union Square': 7, 'Financial District': 9, 'Pacific Heights': 8, 'Bayview': 19},
    'Bayview': {'Embarcadero': 19, 'Richmond District': 25, 'Union Square': 17, 'Financial District': 19, 'Pacific Heights': 23, 'Nob Hill': 20}
}

# Create symmetric travel times by averaging both directions
locations = list(original_travel_times.keys())
symmetric_travel_times = {loc: {} for loc in locations}

for i, loc1 in enumerate(locations):
    for loc2 in locations[i+1:]:
        if loc2 in original_travel_times[loc1]:
            time1 = original_travel_times[loc1][loc2]
            time2 = original_travel_times[loc2][loc1]
            avg_time = round((time1 + time2) / 2)
            symmetric_travel_times[loc1][loc2] = avg_time
            symmetric_travel_times[loc2][loc1] = avg_time

travel_times = symmetric_travel_times

# Start at Embarcadero at 9:00 AM (540 minutes)
current_time = 540
current_location = 'Embarcadero'
itinerary = []

# Meeting with Nancy at Pacific Heights
next_location = 'Pacific Heights'
travel_time = travel_times[current_location][next_location]
current_time += travel_time  # Arrival time at Pacific Heights
nancy_available_start = 8 * 60  # 8:00 AM
nancy_available_end = 11 * 60 + 30  # 11:30 AM
nancy_duration = 90  # minutes
start_time = max(current_time, nancy_available_start)
end_time = start_time + nancy_duration
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Nancy",
    "start_time": format_time(start_time),
    "end_time": format_time(end_time)
})
current_time = end_time
current_location = next_location

# Meeting with Lisa at Union Square
next_location = 'Union Square'
travel_time = travel_times[current_location][next_location]
current_time += travel_time  # Arrival time at Union Square
lisa_available_start = 9 * 60  # 9:00 AM
lisa_available_end = 16 * 60 + 30  # 4:30 PM
lisa_duration = 45  # minutes
start_time = max(current_time, lisa_available_start)
end_time = start_time + lisa_duration
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Lisa",
    "start_time": format_time(start_time),
    "end_time": format_time(end_time)
})
current_time = end_time
current_location = next_location

# Meeting with Joshua at Financial District
next_location = 'Financial District'
travel_time = travel_times[current_location][next_location]
current_time += travel_time  # Arrival time at Financial District
joshua_available_start = 12 * 60  # 12:00 PM
joshua_available_end = 15 * 60 + 15  # 3:15 PM
joshua_duration = 15  # minutes
start_time = max(current_time, joshua_available_start)
end_time = start_time + joshua_duration
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Joshua",
    "start_time": format_time(start_time),
    "end_time": format_time(end_time)
})
current_time = end_time
current_location = next_location

# Wait until departure time to meet John at Bayview (leave Financial District at 16:26)
current_time = 16 * 60 + 26  # 4:26 PM

# Meeting with John at Bayview
next_location = 'Bayview'
travel_time = travel_times[current_location][next_location]
current_time += travel_time  # Arrival time at Bayview
john_available_start = 16 * 60 + 45  # 4:45 PM
john_available_end = 21 * 60 + 30  # 9:30 PM
john_duration = 60  # minutes
start_time = max(current_time, john_available_start)
end_time = start_time + john_duration
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "John",
    "start_time": format_time(start_time),
    "end_time": format_time(end_time)
})
current_time = end_time
current_location = next_location

# Meeting with Andrew at Nob Hill
next_location = 'Nob Hill'
travel_time = travel_times[current_location][next_location]
current_time += travel_time  # Arrival time at Nob Hill
andrew_available_start = 11 * 60 + 30  # 11:30 AM
andrew_available_end = 20 * 60 + 15  # 8:15 PM
andrew_duration = 60  # minutes
start_time = max(current_time, andrew_available_start)
end_time = start_time + andrew_duration
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Andrew",
    "start_time": format_time(start_time),
    "end_time": format_time(end_time)
})
current_time = end_time
current_location = next_location

# Meeting with Kenneth at Pacific Heights (closer location)
next_location = 'Pacific Heights'  # Changed to Pacific Heights for efficiency
travel_time = travel_times[current_location][next_location]  # Only 8 minutes from Nob Hill
current_time += travel_time  # Arrival time at Pacific Heights
kenneth_available_start = 21 * 60 + 15  # 9:15 PM
kenneth_available_end = 22 * 60  # 10:00 PM
kenneth_duration = 30  # minutes
start_time = max(current_time, kenneth_available_start)
end_time = start_time + kenneth_duration
itinerary.append({
    "action": "meet",
    "location": next_location,
    "person": "Kenneth",
    "start_time": format_time(start_time),
    "end_time": format_time(end_time)
})

# Output the itinerary as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))