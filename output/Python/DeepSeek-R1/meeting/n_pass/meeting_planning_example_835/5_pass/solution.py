def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    ampm = 'AM' if hours < 12 else 'PM'
    hours12 = hours % 12
    if hours12 == 0:
        hours12 = 12
    return f"{hours12}:{mins:02d} {ampm}"

def main():
    locations = [
        "Pacific Heights",
        "Golden Gate Park",
        "The Castro",
        "Bayview",
        "Marina District",
        "Union Square",
        "Sunset District",
        "Alamo Square",
        "Financial District",
        "Mission District"
    ]
    
    location_to_index = {loc: idx for idx, loc in enumerate(locations)}
    
    travel_dict = {
        "Pacific Heights": {"Golden Gate Park": 15, "The Castro": 16, "Bayview": 22, "Marina District": 6, "Union Square": 12, "Sunset District": 21, "Alamo Square": 10, "Financial District": 13, "Mission District": 15},
        "Golden Gate Park": {"Pacific Heights": 16, "The Castro": 13, "Bayview": 23, "Marina District": 16, "Union Square": 22, "Sunset District": 10, "Alamo Square": 9, "Financial District": 26, "Mission District": 17},
        "The Castro": {"Pacific Heights": 16, "Golden Gate Park": 11, "Bayview": 19, "Marina District": 21, "Union Square": 19, "Sunset District": 17, "Alamo Square": 8, "Financial District": 21, "Mission District": 7},
        "Bayview": {"Pacific Heights": 23, "Golden Gate Park": 22, "The Castro": 19, "Marina District": 27, "Union Square": 18, "Sunset District": 23, "Alamo Square": 16, "Financial District": 19, "Mission District": 13},
        "Marina District": {"Pacific Heights": 7, "Golden Gate Park": 18, "The Castro": 22, "Bayview": 27, "Union Square": 16, "Sunset District": 19, "Alamo Square": 15, "Financial District": 17, "Mission District": 20},
        "Union Square": {"Pacific Heights": 15, "Golden Gate Park": 22, "The Castro": 17, "Bayview": 15, "Marina District": 18, "Sunset District": 27, "Alamo Square": 15, "Financial District": 9, "Mission District": 14},
        "Sunset District": {"Pacific Heights": 21, "Golden Gate Park": 11, "The Castro": 17, "Bayview": 22, "Marina District": 21, "Union Square": 30, "Alamo Square": 17, "Financial District": 30, "Mission District": 25},
        "Alamo Square": {"Pacific Heights": 10, "Golden Gate Park": 9, "The Castro": 8, "Bayview": 16, "Marina District": 15, "Union Square": 14, "Sunset District": 16, "Financial District": 17, "Mission District": 10},
        "Financial District": {"Pacific Heights": 13, "Golden Gate Park": 23, "The Castro": 20, "Bayview": 19, "Marina District": 15, "Union Square": 9, "Sunset District": 30, "Alamo Square": 17, "Mission District": 17},
        "Mission District": {"Pacific Heights": 16, "Golden Gate Park": 17, "The Castro": 7, "Bayview": 14, "Marina District": 19, "Union Square": 15, "Sunset District": 24, "Alamo Square": 11, "Financial District": 15}
    }
    
    travel_matrix = [[0]*10 for _ in range(10)]
    for i, from_loc in enumerate(locations):
        for j, to_loc in enumerate(locations):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                travel_matrix[i][j] = travel_dict[from_loc][to_loc]
    
    friends = [
        {'name': 'Helen', 'location': 'Golden Gate Park', 'available_start': 570, 'available_end': 735, 'min_duration': 45},
        {'name': 'Steven', 'location': 'The Castro', 'available_start': 1215, 'available_end': 1320, 'min_duration': 105},
        {'name': 'Deborah', 'location': 'Bayview', 'available_start': 510, 'available_end': 720, 'min_duration': 30},
        {'name': 'Matthew', 'location': 'Marina District', 'available_start': 555, 'available_end': 855, 'min_duration': 45},
        {'name': 'Joseph', 'location': 'Union Square', 'available_start': 855, 'available_end': 1125, 'min_duration': 120},
        {'name': 'Ronald', 'location': 'Sunset District', 'available_start': 960, 'available_end': 1245, 'min_duration': 60},
        {'name': 'Robert', 'location': 'Alamo Square', 'available_start': 1110, 'available_end': 1275, 'min_duration': 120},
        {'name': 'Rebecca', 'location': 'Financial District', 'available_start': 885, 'available_end': 975, 'min_duration': 30},
        {'name': 'Elizabeth', 'location': 'Mission District', 'available_start': 1110, 'available_end': 1260, 'min_duration': 120}
    ]
    
    n = len(friends)
    dp = [[10**9] * 10 for _ in range(1<<n)]
    parent = [[None] * 10 for _ in range(1<<n)]
    
    office_index = location_to_index["Financial District"]
    dp[0][office_index] = 540
    
    for mask in range(1<<n):
        for loc in range(10):
            if dp[mask][loc] == 10**9:
                continue
            for i in range(n):
                if mask & (1<<i):
                    continue
                friend_loc_name = friends[i]['location']
                friend_loc = location_to_index[friend_loc_name]
                travel_time = travel_matrix[loc][friend_loc]
                arrival_time = dp[mask][loc] + travel_time
                available_start = friends[i]['available_start']
                available_end = friends[i]['available_end']
                min_duration = friends[i]['min_duration']
                
                meeting_start = max(arrival_time, available_start)
                meeting_end = meeting_start + min_duration
                
                if meeting_end <= available_end:
                    new_mask = mask | (1<<i)
                    if meeting_end < dp[new_mask][friend_loc]:
                        dp[new_mask][friend_loc] = meeting_end
                        parent[new_mask][friend_loc] = (mask, loc, i, meeting_start, meeting_end)
    
    best_mask = None
    best_loc = None
    best_popcount = -1
    for mask in range(1<<n):
        for loc in range(10):
            if dp[mask][loc] == 10**9:
                continue
            return_time = dp[mask][loc] + travel_matrix[loc][office_index]
            if return_time <= 1260:
                popcount = bin(mask).count("1")
                if popcount > best_popcount:
                    best_popcount = popcount
                    best_mask = mask
                    best_loc = loc
    
    if best_popcount == -1:
        return []
    
    itinerary_backwards = []
    current_mask = best_mask
    current_loc = best_loc
    while current_mask != 0:
        if parent[current_mask][current_loc] is None:
            break
        prev_mask, prev_loc, i, meeting_start, meeting_end = parent[current_mask][current_loc]
        friend = friends[i]
        itinerary_backwards.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        current_mask = prev_mask
        current_loc = prev_loc
    
    itinerary_forward = list(reversed(itinerary_backwards))
    
    if current_loc != office_index:
        return_start = dp[best_mask][best_loc]
        travel_time_back = travel_matrix[best_loc][office_index]
        return_end = return_start + travel_time_back
        itinerary_forward.append({
            "action": "return to office",
            "location": "Financial District",
            "start_time": format_time(return_start),
            "end_time": format_time(return_end)
        })
    
    return itinerary_forward