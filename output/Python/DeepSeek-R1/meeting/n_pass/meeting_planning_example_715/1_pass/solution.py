import json

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

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
        [11, 16, 13, 24, 23, 16, 17, 9, 0]
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
    dp = [[None] * n for _ in range(1<<n)]
    parent = [[None] * n for _ in range(1<<n)]
    
    start_time_presidio = 9*60
    for i in range(n):
        loc_index = friends[i]['loc_index']
        travel = travel_time[0][loc_index]
        arrive = start_time_presidio + travel
        start_meeting = max(arrive, friends[i]['start'])
        if start_meeting <= friends[i]['end'] - friends[i]['min_duration']:
            end_meeting = start_meeting + friends[i]['min_duration']
            mask = 1 << i
            dp[mask][i] = end_meeting
            parent[mask][i] = (0, -1, start_meeting, end_meeting)
    
    for mask in range(1<<n):
        for i in range(n):
            if dp[mask][i] is None:
                continue
            current_finish = dp[mask][i]
            for j in range(n):
                if mask & (1 << j):
                    continue
                from_loc = friends[i]['loc_index']
                to_loc = friends[j]['loc_index']
                travel = travel_time[from_loc][to_loc]
                arrive_j = current_finish + travel
                start_j = max(arrive_j, friends[j]['start'])
                if start_j > friends[j]['end'] - friends[j]['min_duration']:
                    continue
                end_j = start_j + friends[j]['min_duration']
                new_mask = mask | (1 << j)
                if dp[new_mask][j] is None or end_j < dp[new_mask][j]:
                    dp[new_mask][j] = end_j
                    parent[new_mask][j] = (mask, i, start_j, end_j)
    
    best_count = -1
    best_mask = None
    best_i = None
    for mask in range(1<<n):
        for i in range(n):
            if dp[mask][i] is not None:
                count = bin(mask).count("1")
                if count > best_count or (count == best_count and best_mask is not None and dp[mask][i] < dp[best_mask][best_i]):
                    best_count = count
                    best_mask = mask
                    best_i = i
    
    itinerary = []
    if best_mask is not None:
        current_mask = best_mask
        current_i = best_i
        while current_mask != 0:
            _, prev_i, start_time_val, end_time_val = parent[current_mask][current_i]
            friend = friends[current_i]
            itinerary.append({
                'action': 'meet',
                'location': ['Presidio', 'Marina District', 'The Castro', 'Fisherman\'s Wharf', 'Bayview', 'Pacific Heights', 'Mission District', 'Alamo Square', 'Golden Gate Park'][friend['loc_index']],
                'person': friend['name'],
                'start_time': min_to_time(start_time_val),
                'end_time': min_to_time(end_time_val)
            })
            if prev_i == -1:
                break
            next_mask, next_i = parent[current_mask][current_i][0], parent[current_mask][current_i][1]
            current_mask, current_i = next_mask, next_i
        itinerary.reverse()
    
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()