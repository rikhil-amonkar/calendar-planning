import json

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    travel_time = [
        [0, 11, 21, 19, 31, 11, 26, 19, 12],
        [10, 0, 22, 10, 27, 7, 20, 15, 18],
        [20, 21, 0, 24, 19, 16, 7, 8, 11],
        [17, 9, 27, 0, 26, 12, 22, 21, 25],
        [32, 27, 19, 25, 0, 23, 13, 16, 22],
        [11, 6, 16, 13, 22, 0, 15, 10, 15],
        [25, 19, 7, 22, 14, 16, 0, 11, 17],
        [17, 15, 8, 19, 16, 10, 10, 0, 9],
        [11, 16, 13, 24, 22, 16, 17, 9, 0]
    ]
    
    friends = [
        {'name': 'Amanda', 'loc_index': 1, 'start': 14*60+45, 'end': 19*60+30, 'min_duration': 105},
        {'name': 'Melissa', 'loc_index': 2, 'start': 9*60+30, 'end': 17*60+0, 'min_duration': 30},
        {'name': 'Jeffrey', 'loc_index': 3, 'start': 12*60+45, 'end': 18*60+45, 'min_duration': 120},
        {'name': 'Matthew', 'loc_index': 4, 'start': 10*60+15, 'end': 13*60+15, 'min_duration': 30},
        {'name': 'Nancy', 'loc_index': 5, 'start': 17*60+0, 'end': 21*60+30, 'min_duration': 105},
        {'name': 'Karen', 'loc_index': 6, 'start': 17*60+30, 'end': 20*60+30, 'min_duration': 105},
        {'name': 'Robert', 'loc_index': 7, 'start': 11*60+15, 'end': 17*60+30, 'min_duration': 120},
        {'name': 'Joseph', 'loc_index': 8, 'start': 8*60+30, 'end': 21*60+15, 'min_duration': 105}
    ]
    
    n = len(friends)
    INF = 10**9
    dp = [[(INF, INF)] * n for _ in range(1<<n)]
    parent = [[None] * n for _ in range(1<<n)]
    
    start_time_presidio = 9*60
    for i in range(n):
        loc_idx = friends[i]['loc_index']
        travel = travel_time[0][loc_idx]
        arrive_time = start_time_presidio + travel
        start_meeting = max(arrive_time, friends[i]['start'])
        if start_meeting <= friends[i]['end'] - friends[i]['min_duration']:
            end_meeting = start_meeting + friends[i]['min_duration']
            mask = 1 << i
            dp[mask][i] = (end_meeting, travel)
            parent[mask][i] = (-1, -1, start_meeting, end_meeting, travel, arrive_time, travel)
    
    for mask in range(1<<n):
        for i in range(n):
            if dp[mask][i][0] == INF:
                continue
            current_end, current_travel = dp[mask][i]
            for j in range(n):
                if mask & (1 << j):
                    continue
                from_loc = friends[i]['loc_index']
                to_loc = friends[j]['loc_index']
                travel_ij = travel_time[from_loc][to_loc]
                arrive_next = current_end + travel_ij
                start_meeting = max(arrive_next, friends[j]['start'])
                if start_meeting > friends[j]['end'] - friends[j]['min_duration']:
                    continue
                end_meeting = start_meeting + friends[j]['min_duration']
                new_travel = current_travel + travel_ij
                new_mask = mask | (1 << j)
                current_val = dp[new_mask][j]
                if end_meeting < current_val[0] or (end_meeting == current_val[0] and new_travel < current_val[1]):
                    dp[new_mask][j] = (end_meeting, new_travel)
                    parent[new_mask][j] = (mask, i, start_meeting, end_meeting, travel_ij, arrive_next, new_travel)
    
    best_count = -1
    best_end_time = INF
    best_travel = INF
    best_mask = 0
    best_index = -1
    for mask in range(1<<n):
        for i in range(n):
            end_time, travel_val = dp[mask][i]
            if end_time == INF:
                continue
            count = bin(mask).count('1')
            if count > best_count or (count == best_count and (end_time < best_end_time or (end_time == best_end_time and travel_val < best_travel))):
                best_count = count
                best_end_time = end_time
                best_travel = travel_val
                best_mask = mask
                best_index = i
    
    itinerary = []
    if best_count > 0:
        mask = best_mask
        i = best_index
        while mask:
            par = parent[mask][i]
            if par[0] == -1:
                start_meeting, end_meeting = par[2], par[3]
                travel = par[4]
                arrive = par[5]
                friend = friends[i]
                location_name = ['Presidio', 'Marina District', 'The Castro', 'Fisherman\'s Wharf', 'Bayview', 'Pacific Heights', 'Mission District', 'Alamo Square', 'Golden Gate Park'][friend['loc_index']]
                itinerary.append({
                    'action': 'meet',
                    'location': location_name,
                    'person': friend['name'],
                    'start_time': min_to_time(start_meeting),
                    'end_time': min_to_time(end_meeting)
                })
                mask = 0
                continue
            prev_mask, prev_i, start_meeting, end_meeting, travel, arrive, total_travel = par
            friend = friends[i]
            location_name = ['Presidio', 'Marina District', 'The Castro', 'Fisherman\'s Wharf', 'Bayview', 'Pacific Heights', 'Mission District', 'Alamo Square', 'Golden Gate Park'][friend['loc_index']]
            itinerary.append({
                'action': 'meet',
                'location': location_name,
                'person': friend['name'],
                'start_time': min_to_time(start_meeting),
                'end_time': min_to_time(end_meeting)
            })
            mask = prev_mask
            i = prev_i
        itinerary.reverse()
    
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()