import heapq
import json

def main():
    # Define locations and their indices
    locations = [
        "Haight-Ashbury",
        "Mission District",
        "Union Square",
        "Pacific Heights",
        "Bayview",
        "Fisherman's Wharf",
        "Marina District",
        "Richmond District",
        "Sunset District",
        "Golden Gate Park"
    ]
    
    # Travel time matrix (10x10) in minutes
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
    
    # Friend definitions: name, start_avail (minutes from 9:00), end_avail (minutes from 9:00), duration (minutes)
    friends = [
        {'name': 'Elizabeth', 'start': 90, 'end': 660, 'duration': 90},   # 10:30AM to 8:00PM, 90 min
        {'name': 'David', 'start': 375, 'end': 600, 'duration': 45},      # 3:15PM to 7:00PM, 45 min
        {'name': 'Sandra', 'start': 0, 'end': 660, 'duration': 120},      # 7:00AM to 8:00PM, 120 min
        {'name': 'Thomas', 'start': 630, 'end': 690, 'duration': 30},      # 7:30PM to 8:30PM, 30 min
        {'name': 'Robert', 'start': 60, 'end': 360, 'duration': 15},       # 10:00AM to 3:00PM, 15 min
        {'name': 'Kenneth', 'start': 105, 'end': 240, 'duration': 45},     # 10:45AM to 1:00PM, 45 min
        {'name': 'Melissa', 'start': 555, 'end': 660, 'duration': 15},     # 6:15PM to 8:00PM, 15 min
        {'name': 'Kimberly', 'start': 75, 'end': 555, 'duration': 105},    # 10:15AM to 6:15PM, 105 min
        {'name': 'Amanda', 'start': 0, 'end': 585, 'duration': 15}        # 7:45AM to 6:45PM, 15 min
    ]
    
    # Map location index to friend index (location 0 has no friend)
    friend_at_location = [None] * 10
    for i in range(1, 10):
        friend_at_location[i] = i - 1  # location i has friend i-1
    
    n = len(friends)  # 9 friends
    num_masks = 1 << n
    INF = 10**9
    
    # Initialize distance and parent arrays
    dist = [[INF] * 10 for _ in range(num_masks)]
    parent = [[None] * 10 for _ in range(num_masks)]
    
    # Priority queue: (time, mask, location)
    heap = []
    dist[0][0] = 0
    heapq.heappush(heap, (0, 0, 0))
    
    # Dijkstra-like algorithm
    while heap:
        d, mask, loc = heapq.heappop(heap)
        if d != dist[mask][loc]:
            continue
        
        # Option 1: Meet friend at current location (if exists and not met)
        if loc != 0:  # location 0 has no friend
            friend_idx = friend_at_location[loc]
            if friend_idx is not None and (mask & (1 << friend_idx)) == 0:
                friend = friends[friend_idx]
                start_time = max(d, friend['start'])
                end_time = start_time + friend['duration']
                if end_time <= friend['end']:
                    new_mask = mask | (1 << friend_idx)
                    if end_time < dist[new_mask][loc]:
                        dist[new_mask][loc] = end_time
                        heapq.heappush(heap, (end_time, new_mask, loc))
                        parent[new_mask][loc] = (mask, loc, 'meet', friend_idx, start_time, end_time)
        
        # Option 2: Travel to other locations
        for next_loc in range(10):
            if next_loc == loc:
                continue
            t = travel_time[loc][next_loc]
            new_time = d + t
            if new_time < dist[mask][next_loc]:
                dist[mask][next_loc] = new_time
                heapq.heappush(heap, (new_time, mask, next_loc))
                parent[mask][next_loc] = (mask, loc, 'travel', None)
    
    # Find best state: max meetings, then min time
    best_mask = best_loc = -1
    best_count = -1
    best_time = INF
    for mask in range(num_masks):
        for loc in range(10):
            if dist[mask][loc] == INF:
                continue
            count = bin(mask).count('1')
            if count > best_count or (count == best_count and dist[mask][loc] < best_time):
                best_count = count
                best_time = dist[mask][loc]
                best_mask = mask
                best_loc = loc
    
    # Backtrack to collect meetings
    meetings = []
    mask, loc = best_mask, best_loc
    while parent[mask][loc] is not None:
        prev_mask, prev_loc, action, *rest = parent[mask][loc]
        if action == 'meet':
            friend_idx, start_time, end_time = rest
            meetings.append((friend_idx, start_time, end_time))
            mask, loc = prev_mask, prev_loc
        else:  # travel
            mask, loc = prev_mask, prev_loc
    
    # Convert meetings to itinerary (reverse to chronological order)
    itinerary = []
    for friend_idx, start_time, end_time in reversed(meetings):
        friend = friends[friend_idx]
        # Convert minutes from 9:00 to absolute time string
        def format_time(minutes):
            total_min = 9 * 60 + minutes
            h = total_min // 60
            m = total_min % 60
            return f"{h}:{m:02d}"
        
        itinerary.append({
            "action": "meet",
            "location": locations[friend_idx + 1],  # friend at location friend_idx+1
            "person": friend['name'],
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()