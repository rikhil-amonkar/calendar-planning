import json

def main():
    travel_time = [
        [0, 11, 19, 12, 18, 23, 17, 10, 15, 7],
        [12, 0, 15, 16, 14, 22, 19, 20, 24, 17],
        [18, 14, 0, 15, 15, 15, 18, 20, 27, 22],
        [11, 15, 12, 0, 22, 13, 6, 12, 21, 15],
        [19, 13, 18, 23, 0, 25, 27, 25, 23, 22],
        [22, 22, 13, 12, 26, 0, 9, 18, 27, 25],
        [16, 20, 16, 7, 27, 10, 0, 11, 19, 18],
        [10, 20, 21, 10, 27, 18, 9, 0, 11, 9],
        [15, 25, 30, 21, 22, 29, 21, 12, 0, 11],
        [7, 17, 22, 16, 23, 24, 16, 7, 10, 0]
    ]
    
    friends = [
        {"name": "Elizabeth", "location": "Mission District", "location_index": 1, "start": 630, "end": 1200, "min_duration": 90},
        {"name": "David", "location": "Union Square", "location_index": 2, "start": 915, "end": 1140, "min_duration": 45},
        {"name": "Sandra", "location": "Pacific Heights", "location_index": 3, "start": 420, "end": 1200, "min_duration": 120},
        {"name": "Thomas", "location": "Bayview", "location_index": 4, "start": 1170, "end": 1230, "min_duration": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", "location_index": 5, "start": 600, "end": 900, "min_duration": 15},
        {"name": "Kenneth", "location": "Marina District", "location_index": 6, "start": 645, "end": 780, "min_duration": 45},
        {"name": "Melissa", "location": "Richmond District", "location_index": 7, "start": 1095, "end": 1200, "min_duration": 15},
        {"name": "Kimberly", "location": "Sunset District", "location_index": 8, "start": 615, "end": 1095, "min_duration": 105},
        {"name": "Amanda", "location": "Golden Gate Park", "location_index": 9, "start": 465, "end": 1125, "min_duration": 15}
    ]
    
    n = 1 << 9
    dp = [[10**9] * 10 for _ in range(n)]
    parent = [[None] * 10 for _ in range(n)]
    
    dp[0][0] = 540
    
    for mask in range(n):
        for loc in range(10):
            if dp[mask][loc] == 10**9:
                continue
            current_time = dp[mask][loc]
            for j in range(9):
                if mask & (1 << j) != 0:
                    continue
                loc_j = friends[j]['location_index']
                travel = travel_time[loc][loc_j]
                arrival = current_time + travel
                start_meeting = max(arrival, friends[j]['start'])
                end_meeting = start_meeting + friends[j]['min_duration']
                if end_meeting > friends[j]['end']:
                    continue
                new_mask = mask | (1 << j)
                if end_meeting < dp[new_mask][loc_j]:
                    dp[new_mask][loc_j] = end_meeting
                    parent[new_mask][loc_j] = (mask, loc, j, start_meeting, end_meeting)
    
    best_count = -1
    best_mask = None
    best_loc = None
    for mask in range(n):
        for loc in range(10):
            if dp[mask][loc] < 10**9:
                count = bin(mask).count('1')
                if count > best_count:
                    best_count = count
                    best_mask = mask
                    best_loc = loc
    
    itinerary = []
    mask = best_mask
    loc = best_loc
    while mask != 0:
        prev_mask, prev_loc, j, start_meeting, end_meeting = parent[mask][loc]
        itinerary.append({
            "action": "meet",
            "location": friends[j]["location"],
            "person": friends[j]["name"],
            "start_time": f"{start_meeting // 60}:{start_meeting % 60:02d}",
            "end_time": f"{end_meeting // 60}:{end_meeting % 60:02d}"
        })
        mask = prev_mask
        loc = prev_loc
    
    itinerary.reverse()
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()