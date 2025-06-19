import heapq
import json

def format_time(minutes):
    h = 9 + minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
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
        {'name': 'Elizabeth', 'start': 90, 'end': 660, 'duration': 90},
        {'name': 'David', 'start': 375, 'end': 600, 'duration': 45},
        {'name': 'Sandra', 'start': 0, 'end': 660, 'duration': 120},
        {'name': 'Thomas', 'start': 630, 'end': 690, 'duration': 30},
        {'name': 'Robert', 'start': 60, 'end': 360, 'duration': 15},
        {'name': 'Kenneth', 'start': 105, 'end': 240, 'duration': 45},
        {'name': 'Melissa', 'start': 555, 'end': 660, 'duration': 15},
        {'name': 'Kimberly', 'start': 75, 'end': 555, 'duration': 105},
        {'name': 'Amanda', 'start': 0, 'end': 585, 'duration': 15}
    ]
    
    friend_at_location = [None] * 10
    for i in range(1, 10):
        friend_at_location[i] = i - 1
        
    n = len(friends)
    num_masks = 1 << n
    INF = 10**9
    
    dist = [[INF] * 10 for _ in range(num_masks)]
    parent = [[None] * 10 for _ in range(num_masks)]
    
    heap = []
    dist[0][0] = 0
    heapq.heappush(heap, (0, 0, 0))
    
    while heap:
        d, mask, loc = heapq.heappop(heap)
        if d != dist[mask][loc]:
            continue
            
        if loc != 0:
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
        
        for next_loc in range(10):
            if next_loc == loc:
                continue
            t = travel_time[loc][next_loc]
            new_time = d + t
            if new_time < dist[mask][next_loc]:
                dist[mask][next_loc] = new_time
                heapq.heappush(heap, (new_time, mask, next_loc))
                parent[mask][next_loc] = (mask, loc, 'travel', None, d, new_time)
    
    best_mask = 0
    best_time = INF
    best_count = -1
    for mask in range(num_masks):
        time_here = dist[mask][0]
        if time_here > 720:
            continue
        count = bin(mask).count('1')
        if count > best_count or (count == best_count and time_here < best_time):
            best_count = count
            best_time = time_here
            best_mask = mask
                
    actions = []
    mask = best_mask
    loc = 0
    while parent[mask][loc] is not None:
        prev_mask, prev_loc, action_type, *rest = parent[mask][loc]
        if action_type == 'travel':
            _, start_t, end_t = rest
            actions.append({
                "action": "travel",
                "from": locations[prev_loc],
                "to": locations[loc],
                "start_time": format_time(start_t),
                "end_time": format_time(end_t)
            })
            mask, loc = prev_mask, prev_loc
        elif action_type == 'meet':
            friend_idx, start_meet, end_meet = rest
            actions.append({
                "action": "meet",
                "location": locations[loc],
                "person": friends[friend_idx]['name'],
                "start_time": format_time(start_meet),
                "end_time": format_time(end_meet)
            })
            mask = prev_mask
    
    actions.reverse()
    result = {"itinerary": actions}
    print(json.dumps(result))

if __name__ == '__main__':
    main()