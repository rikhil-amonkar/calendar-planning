import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    travel = {
        "Sunset District": {"Presidio": 16, "Nob Hill": 27, "Pacific Heights": 21, "Mission District": 25, "Marina District": 21, "North Beach": 28, "Russian Hill": 24, "Richmond District": 12, "Embarcadero": 30, "Alamo Square": 17},
        "Presidio": {"Sunset District": 15, "Nob Hill": 18, "Pacific Heights": 11, "Mission District": 26, "Marina District": 11, "North Beach": 18, "Russian Hill": 14, "Richmond District": 7, "Embarcadero": 20, "Alamo Square": 19},
        "Nob Hill": {"Sunset District": 24, "Presidio": 17, "Pacific Heights": 8, "Mission District": 13, "Marina District": 11, "North Beach": 8, "Russian Hill": 5, "Richmond District": 14, "Embarcadero": 9, "Alamo Square": 11},
        "Pacific Heights": {"Sunset District": 21, "Presidio": 11, "Nob Hill": 8, "Mission District": 15, "Marina District": 6, "North Beach": 9, "Russian Hill": 7, "Richmond District": 12, "Embarcadero": 10, "Alamo Square": 10},
        "Mission District": {"Sunset District": 24, "Presidio": 25, "Nob Hill": 12, "Pacific Heights": 16, "Marina District": 19, "North Beach": 17, "Russian Hill": 15, "Richmond District": 20, "Embarcadero": 19, "Alamo Square": 11},
        "Marina District": {"Sunset District": 19, "Presidio": 10, "Nob Hill": 12, "Pacific Heights": 7, "Mission District": 20, "North Beach": 11, "Russian Hill": 8, "Richmond District": 11, "Embarcadero": 14, "Alamo Square": 15},
        "North Beach": {"Sunset District": 27, "Presidio": 17, "Nob Hill": 7, "Pacific Heights": 8, "Mission District": 18, "Marina District": 9, "Russian Hill": 4, "Richmond District": 18, "Embarcadero": 6, "Alamo Square": 16},
        "Russian Hill": {"Sunset District": 23, "Presidio": 14, "Nob Hill": 5, "Pacific Heights": 7, "Mission District": 16, "Marina District": 7, "North Beach": 5, "Richmond District": 14, "Embarcadero": 8, "Alamo Square": 15},
        "Richmond District": {"Sunset District": 11, "Presidio": 7, "Nob Hill": 17, "Pacific Heights": 10, "Mission District": 20, "Marina District": 9, "North Beach": 17, "Russian Hill": 13, "Embarcadero": 19, "Alamo Square": 13},
        "Embarcadero": {"Sunset District": 30, "Presidio": 20, "Nob Hill": 10, "Pacific Heights": 11, "Mission District": 20, "Marina District": 12, "North Beach": 5, "Russian Hill": 8, "Richmond District": 21, "Alamo Square": 19},
        "Alamo Square": {"Sunset District": 16, "Presidio": 17, "Nob Hill": 11, "Pacific Heights": 10, "Mission District": 10, "Marina District": 15, "North Beach": 15, "Russian Hill": 13, "Richmond District": 11, "Embarcadero": 16}
    }
    
    friends = [
        {'name': 'Charles', 'location': 'Presidio', 'start': 795, 'end': 900, 'min_duration': 105},
        {'name': 'Robert', 'location': 'Nob Hill', 'start': 795, 'end': 1050, 'min_duration': 90},
        {'name': 'Nancy', 'location': 'Pacific Heights', 'start': 885, 'end': 1320, 'min_duration': 105},
        {'name': 'Brian', 'location': 'Mission District', 'start': 930, 'end': 1320, 'min_duration': 60},
        {'name': 'Kimberly', 'location': 'Marina District', 'start': 1020, 'end': 1185, 'min_duration': 75},
        {'name': 'David', 'location': 'North Beach', 'start': 885, 'end': 990, 'min_duration': 75},
        {'name': 'William', 'location': 'Russian Hill', 'start': 750, 'end': 1155, 'min_duration': 120},
        {'name': 'Jeffrey', 'location': 'Richmond District', 'start': 720, 'end': 1155, 'min_duration': 45},
        {'name': 'Karen', 'location': 'Embarcadero', 'start': 855, 'end': 1245, 'min_duration': 60},
        {'name': 'Joshua', 'location': 'Alamo Square', 'start': 1125, 'end': 1320, 'min_duration': 60}
    ]
    
    n = len(friends)
    dp = {}
    parent = {}
    
    start_state = (0, 'Sunset District')
    dp[start_state] = 540  # 9:00 AM in minutes
    parent[start_state] = None
    
    masks_by_popcount = [[] for _ in range(n+1)]
    for mask in range(1 << n):
        cnt = bin(mask).count("1")
        masks_by_popcount[cnt].append(mask)
    
    for cnt in range(0, n+1):
        for mask in masks_by_popcount[cnt]:
            for loc in travel.keys():
                state = (mask, loc)
                if state not in dp:
                    continue
                current_time = dp[state]
                for j in range(n):
                    if mask & (1 << j):
                        continue
                    friend = friends[j]
                    from_loc = loc
                    to_loc = friend['location']
                    tt = travel[from_loc][to_loc]
                    arrival = current_time + tt
                    meeting_start = max(arrival, friend['start'])
                    meeting_end = meeting_start + friend['min_duration']
                    if meeting_end > friend['end']:
                        continue
                    new_mask = mask | (1 << j)
                    new_state = (new_mask, to_loc)
                    if new_state not in dp or meeting_end < dp[new_state]:
                        dp[new_state] = meeting_end
                        parent[new_state] = (mask, loc, j, meeting_start, meeting_end)
    
    best_state = None
    best_count = -1
    best_time = float('inf')
    for state, time_val in dp.items():
        mask, loc = state
        cnt = bin(mask).count("1")
        if cnt > best_count or (cnt == best_count and time_val < best_time):
            best_count = cnt
            best_time = time_val
            best_state = state
    
    itinerary = []
    current_state = best_state
    while current_state in parent and parent[current_state] is not None:
        mask, loc = current_state
        prev_mask, prev_loc, j, start_time, end_time = parent[current_state]
        itinerary.append({
            "action": "meet",
            "location": friends[j]['location'],
            "person": friends[j]['name'],
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        current_state = (prev_mask, prev_loc)
    
    itinerary.reverse()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()