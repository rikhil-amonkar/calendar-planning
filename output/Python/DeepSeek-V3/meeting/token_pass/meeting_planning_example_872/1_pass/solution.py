import json
from itertools import permutations

def time_to_min(t_str):
    """Convert '9:00AM' or '9:00PM' to minutes since midnight."""
    t_str = t_str.strip()
    is_pm = 'PM' in t_str
    time_part = t_str.replace('AM', '').replace('PM', '').strip()
    h, m = map(int, time_part.split(':'))
    if is_pm and h != 12:
        h += 12
    if not is_pm and h == 12:
        h = 0
    return h * 60 + m

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times dictionary
travel = {
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Marina District'): 11,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Marina District'): 12,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
}

# Friend data: name, location, start_available, end_available, min_duration (minutes)
friends = [
    ("Karen", "Haight-Ashbury", time_to_min("9:00PM"), time_to_min("9:45PM"), 45),
    ("Jessica", "Nob Hill", time_to_min("1:45PM"), time_to_min("9:00PM"), 90),
    ("Brian", "Russian Hill", time_to_min("3:30PM"), time_to_min("9:45PM"), 60),
    ("Kenneth", "North Beach", time_to_min("9:45AM"), time_to_min("9:00PM"), 30),
    ("Jason", "Chinatown", time_to_min("8:15AM"), time_to_min("11:45AM"), 75),
    ("Stephanie", "Union Square", time_to_min("2:45PM"), time_to_min("6:45PM"), 105),
    ("Kimberly", "Embarcadero", time_to_min("9:45AM"), time_to_min("7:30PM"), 75),
    ("Steven", "Financial District", time_to_min("7:15AM"), time_to_min("9:15PM"), 60),
    ("Mark", "Marina District", time_to_min("10:15AM"), time_to_min("1:00PM"), 75),
]

start_loc = "Presidio"
start_time = time_to_min("9:00AM")

best_count = 0
best_meetings = []
best_total_time = 0

def dfs(current_loc, current_time, met, meetings):
    global best_count, best_meetings, best_total_time
    # Try to add any un-met friend
    improved = False
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        if met[i]:
            continue
        travel_time = travel[(current_loc, loc)]
        arrival = current_time + travel_time
        start_meeting = max(arrival, avail_start)
        if start_meeting + min_dur <= avail_end:
            # Schedule this meeting
            met[i] = True
            meetings.append((name, loc, start_meeting, start_meeting + min_dur))
            dfs(loc, start_meeting + min_dur, met, meetings)
            meetings.pop()
            met[i] = False
            improved = True
    # If no one else can be met, check if this is best
    if not improved:
        count = sum(met)
        total_time = sum(end - start for _, _, start, end in meetings)
        if count > best_count or (count == best_count and total_time > best_total_time):
            best_count = count
            best_total_time = total_time
            best_meetings = meetings.copy()

# Run DFS
met = [False] * len(friends)
dfs(start_loc, start_time, met, [])

# Convert best_meetings to itinerary
itinerary = []
for name, loc, start, end in best_meetings:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": min_to_time(start),
        "end_time": min_to_time(end)
    })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))