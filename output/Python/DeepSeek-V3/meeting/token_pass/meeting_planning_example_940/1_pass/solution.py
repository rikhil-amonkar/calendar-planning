import json
from itertools import permutations

def time_to_minutes(t):
    """Convert '9:00AM' or '8:45PM' to minutes since midnight."""
    if 'AM' in t:
        hour_min = t.replace('AM', '').strip()
        hour, minute = map(int, hour_min.split(':'))
        if hour == 12:
            hour = 0
        return hour * 60 + minute
    else:  # PM
        hour_min = t.replace('PM', '').strip()
        hour, minute = map(int, hour_min.split(':'))
        if hour != 12:
            hour += 12
        return hour * 60 + minute

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times dictionary
travel_times = {
    "Union Square": {
        "Mission District": 14, "Fisherman's Wharf": 15, "Russian Hill": 13,
        "Marina District": 18, "North Beach": 10, "Chinatown": 7,
        "Pacific Heights": 15, "The Castro": 17, "Nob Hill": 9, "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15, "Fisherman's Wharf": 22, "Russian Hill": 15,
        "Marina District": 19, "North Beach": 17, "Chinatown": 16,
        "Pacific Heights": 16, "The Castro": 7, "Nob Hill": 12, "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "Mission District": 22, "Russian Hill": 7,
        "Marina District": 9, "North Beach": 6, "Chinatown": 12,
        "Pacific Heights": 12, "The Castro": 27, "Nob Hill": 11, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Mission District": 16, "Fisherman's Wharf": 7,
        "Marina District": 7, "North Beach": 5, "Chinatown": 9,
        "Pacific Heights": 7, "The Castro": 21, "Nob Hill": 5, "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16, "Mission District": 20, "Fisherman's Wharf": 10,
        "Russian Hill": 8, "North Beach": 11, "Chinatown": 15,
        "Pacific Heights": 7, "The Castro": 22, "Nob Hill": 12, "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7, "Mission District": 18, "Fisherman's Wharf": 5,
        "Russian Hill": 4, "Marina District": 9, "Chinatown": 6,
        "Pacific Heights": 8, "The Castro": 23, "Nob Hill": 7, "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7, "Mission District": 17, "Fisherman's Wharf": 8,
        "Russian Hill": 7, "Marina District": 12, "North Beach": 3,
        "Pacific Heights": 10, "The Castro": 22, "Nob Hill": 9, "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12, "Mission District": 15, "Fisherman's Wharf": 13,
        "Russian Hill": 7, "Marina District": 6, "North Beach": 9,
        "Chinatown": 11, "The Castro": 16, "Nob Hill": 8, "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19, "Mission District": 7, "Fisherman's Wharf": 24,
        "Russian Hill": 18, "Marina District": 21, "North Beach": 20,
        "Chinatown": 22, "Pacific Heights": 16, "Nob Hill": 16, "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7, "Mission District": 13, "Fisherman's Wharf": 10,
        "Russian Hill": 5, "Marina District": 11, "North Beach": 8,
        "Chinatown": 6, "Pacific Heights": 8, "The Castro": 17, "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30, "Mission District": 25, "Fisherman's Wharf": 29,
        "Russian Hill": 24, "Marina District": 21, "North Beach": 28,
        "Chinatown": 30, "Pacific Heights": 21, "The Castro": 17, "Nob Hill": 27
    }
}

# Friends data: name, location, window_start, window_end, min_duration (all in minutes)
friends = [
    ("Kevin", "Mission District", time_to_minutes("8:45PM"), time_to_minutes("9:45PM"), 60),
    ("Mark", "Fisherman's Wharf", time_to_minutes("5:15PM"), time_to_minutes("8:00PM"), 90),
    ("Jessica", "Russian Hill", time_to_minutes("9:00AM"), time_to_minutes("3:00PM"), 120),
    ("Jason", "Marina District", time_to_minutes("3:15PM"), time_to_minutes("9:45PM"), 120),
    ("John", "North Beach", time_to_minutes("9:45AM"), time_to_minutes("6:00PM"), 15),
    ("Karen", "Chinatown", time_to_minutes("4:45PM"), time_to_minutes("7:00PM"), 75),
    ("Sarah", "Pacific Heights", time_to_minutes("5:30PM"), time_to_minutes("6:15PM"), 45),
    ("Amanda", "The Castro", time_to_minutes("8:00PM"), time_to_minutes("9:15PM"), 60),
    ("Nancy", "Nob Hill", time_to_minutes("9:45AM"), time_to_minutes("1:00PM"), 45),
    ("Rebecca", "Sunset District", time_to_minutes("8:45AM"), time_to_minutes("3:00PM"), 75)
]

# Start state
start_location = "Union Square"
start_time = time_to_minutes("9:00AM")

best_schedule = []
best_count = 0
best_total_minutes = 0

def dfs(current_location, current_time, visited, schedule):
    global best_schedule, best_count, best_total_minutes
    
    # Try to add any unvisited friend
    for idx, (name, loc, win_start, win_end, min_dur) in enumerate(friends):
        if visited[idx]:
            continue
        
        travel = travel_times[current_location][loc]
        arrive = current_time + travel
        meet_start = max(arrive, win_start)
        if meet_start + min_dur <= win_end:
            # Can meet
            visited[idx] = True
            schedule.append((name, loc, meet_start, meet_start + min_dur))
            
            # Update best
            if len(schedule) > best_count or (len(schedule) == best_count and
                sum(e - s for _, _, s, e in schedule) > best_total_minutes):
                best_count = len(schedule)
                best_total_minutes = sum(e - s for _, _, s, e in schedule)
                best_schedule = schedule.copy()
            
            # Recurse
            dfs(loc, meet_start + min_dur, visited, schedule)
            
            # Backtrack
            schedule.pop()
            visited[idx] = False

# Run DFS
visited = [False] * len(friends)
dfs(start_location, start_time, visited, [])

# Convert best_schedule to required JSON format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))