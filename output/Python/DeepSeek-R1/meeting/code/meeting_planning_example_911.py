import json

def time_to_minutes(t_str):
    parts = t_str.replace('AM', '').replace('PM', '').strip().split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    if 'PM' in t_str and hours != 12:
        hours += 12
    if 'AM' in t_str and hours == 12:
        hours = 0
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        "name": "Steven",
        "location": "North Beach",
        "start": time_to_minutes("5:30PM"),
        "end": time_to_minutes("8:30PM"),
        "duration": 15
    },
    {
        "name": "Sarah",
        "location": "Golden Gate Park",
        "start": time_to_minutes("5:00PM"),
        "end": time_to_minutes("7:15PM"),
        "duration": 75
    },
    {
        "name": "Brian",
        "location": "Embarcadero",
        "start": time_to_minutes("2:15PM"),
        "end": time_to_minutes("4:00PM"),
        "duration": 105
    },
    {
        "name": "Stephanie",
        "location": "Haight-Ashbury",
        "start": time_to_minutes("10:15AM"),
        "end": time_to_minutes("12:15PM"),
        "duration": 75
    },
    {
        "name": "Melissa",
        "location": "Richmond District",
        "start": time_to_minutes("2:00PM"),
        "end": time_to_minutes("7:30PM"),
        "duration": 30
    },
    {
        "name": "Nancy",
        "location": "Nob Hill",
        "start": time_to_minutes("8:15AM"),
        "end": time_to_minutes("12:45PM"),
        "duration": 90
    },
    {
        "name": "David",
        "location": "Marina District",
        "start": time_to_minutes("11:15AM"),
        "end": time_to_minutes("1:15PM"),
        "duration": 120
    },
    {
        "name": "James",
        "location": "Presidio",
        "start": time_to_minutes("3:00PM"),
        "end": time_to_minutes("6:15PM"),
        "duration": 120
    },
    {
        "name": "Elizabeth",
        "location": "Union Square",
        "start": time_to_minutes("11:30AM"),
        "end": time_to_minutes("9:00PM"),
        "duration": 60
    },
    {
        "name": "Robert",
        "location": "Financial District",
        "start": time_to_minutes("1:15PM"),
        "end": time_to_minutes("3:15PM"),
        "duration": 45
    }
]

travel_times = {
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Financial District"): 21,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Financial District"): 8,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Financial District"): 26,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Marina District"): 12,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Financial District"): 17,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Financial District"): 23,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Financial District"): 9,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9
}

def get_travel_time(from_loc, to_loc):
    return travel_times.get((from_loc, to_loc), float('inf'))

current_location = "The Castro"
current_time = time_to_minutes("9:00AM")
itinerary = []

sorted_friends = sorted(friends, key=lambda x: (x['end'], -x['duration']))

for friend in sorted_friends:
    travel_time = get_travel_time(current_location, friend['location'])
    arrival_time = current_time + travel_time
    earliest_start = max(arrival_time, friend['start'])
    latest_start = friend['end'] - friend['duration']
    if earliest_start > latest_start:
        continue
    schedule_start = earliest_start
    schedule_end = schedule_start + friend['duration']
    if schedule_end > friend['end']:
        continue
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time(schedule_start),
        "end_time": minutes_to_time(schedule_end)
    })
    current_time = schedule_end
    current_location = friend['location']

output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))