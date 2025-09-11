import itertools
import json

def parse_time(time_str):
    time_str = time_str.upper().replace(' ', '')
    if 'AM' in time_str:
        time_str = time_str.replace('AM', '')
        parts = time_str.split(':')
        hour = int(parts[0])
        if hour == 12:
            hour = 0
        minutes = int(parts[1])
        return hour * 60 + minutes
    else:
        time_str = time_str.replace('PM', '')
        parts = time_str.split(':')
        hour = int(parts[0])
        if hour != 12:
            hour += 12
        minutes = int(parts[1])
        return hour * 60 + minutes

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel matrix
travel_matrix = {
    "Presidio": {
        "Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18,
        "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19,
        "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21,
        "Marina District": 17
    },
    "Nob Hill": {
        "Presidio": 17, "Haight-Ashbury": 13, "Russian Hill": 5, "North Beach": 8,
        "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9,
        "Marina District": 11
    },
    "Russian Hill": {
        "Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5,
        "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11,
        "Marina District": 7
    },
    "North Beach": {
        "Presidio": 17, "Haight-Ashbury": 18, "Nob Hill": 7, "Russian Hill": 4,
        "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8,
        "Marina District": 9
    },
    "Chinatown": {
        "Presidio": 19, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 7,
        "North Beach": 3, "Union Square": 7, "Embarcadero": 5, "Financial District": 5,
        "Marina District": 12
    },
    "Union Square": {
        "Presidio": 24, "Haight-Ashbury": 18, "Nob Hill": 9, "Russian Hill": 13,
        "North Beach": 10, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9,
        "Marina District": 18
    },
    "Embarcadero": {
        "Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 10, "Russian Hill": 8,
        "North Beach": 5, "Chinatown": 7, "Union Square": 10, "Financial District": 5,
        "Marina District": 12
    },
    "Financial District": {
        "Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 11,
        "North Beach": 7, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4,
        "Marina District": 15
    },
    "Marina District": {
        "Presidio": 10, "Haight-Ashbury": 16, "Nob Hill": 12, "Russian Hill": 8,
        "North Beach": 11, "Chinatown": 15, "Union Square": 16, "Embarcadero": 14,
        "Financial District": 17
    }
}

# Define meetings with constraints
meetings = [
    {"person": "Karen", "location": "Haight-Ashbury", "start_avail": "9:00PM", "end_avail": "9:45PM", "min_duration": 45},
    {"person": "Jessica", "location": "Nob Hill", "start_avail": "1:45PM", "end_avail": "9:00PM", "min_duration": 90},
    {"person": "Brian", "location": "Russian Hill", "start_avail": "3:30PM", "end_avail": "9:45PM", "min_duration": 60},
    {"person": "Kenneth", "location": "North Beach", "start_avail": "9:45AM", "end_avail": "9:00PM", "min_duration": 30},
    {"person": "Jason", "location": "Chinatown", "start_avail": "8:15AM", "end_avail": "11:45AM", "min_duration": 75},
    {"person": "Stephanie", "location": "Union Square", "start_avail": "2:45PM", "end_avail": "6:45PM", "min_duration": 105},
    {"person": "Kimberly", "location": "Embarcadero", "start_avail": "9:45AM", "end_avail": "7:30PM", "min_duration": 75},
    {"person": "Steven", "location": "Financial District", "start_avail": "7:15AM", "end_avail": "9:15PM", "min_duration": 60},
    {"person": "Mark", "location": "Marina District", "start_avail": "10:15AM", "end_avail": "1:00PM", "min_duration": 75}
]

# Convert time strings to minutes
for meeting in meetings:
    meeting['start_avail_min'] = parse_time(meeting['start_avail'])
    meeting['end_avail_min'] = parse_time(meeting['end_avail'])

# Initialize variables
start_time_min = parse_time("9:00AM")
best_count = 0
best_itinerary = []
all_meetings = meetings

# Generate all permutations of meetings
for perm in itertools.permutations(all_meetings):
    current_time = start_time_min
    current_location = "Presidio"
    count = 0
    itinerary = []
    for meeting in perm:
        travel_time = travel_matrix[current_location][meeting['location']]
        arrival_time = current_time + travel_time
        start_avail = meeting['start_avail_min']
        end_avail = meeting['end_avail_min']
        min_duration = meeting['min_duration']
        proposed_start = max(arrival_time, start_avail)
        proposed_end = proposed_start + min_duration
        if proposed_end <= end_avail:
            itinerary.append({
                'meeting': meeting,
                'start': proposed_start,
                'end': proposed_end
            })
            current_time = proposed_end
            current_location = meeting['location']
            count += 1
        else:
            current_time = arrival_time
            current_location = meeting['location']
    if count > best_count:
        best_count = count
        best_itinerary = itinerary

# Format the best itinerary as JSON
formatted_itinerary = []
for item in best_itinerary:
    meeting = item['meeting']
    formatted_itinerary.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['person'],
        "start_time": minutes_to_time(item['start']),
        "end_time": minutes_to_time(item['end'])
    })

output = {"itinerary": formatted_itinerary}
print(json.dumps(output, indent=2))