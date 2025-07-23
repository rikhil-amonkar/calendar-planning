# SOLUTION:
import sys
import json

def main():
    # Travel time matrix (9x9) - indices: 
    # 0: Presidio, 1: Marina District, 2: The Castro, 3: Fisherman's Wharf, 
    # 4: Bayview, 5: Pacific Heights, 6: Mission District, 7: Alamo Square, 8: Golden Gate Park
    n = 9
    travel = [[0] * n for _ in range(n)]
    
    # Set travel times
    travel[0][1] = 11
    travel[0][2] = 21
    travel[0][3] = 19
    travel[0][4] = 31
    travel[0][5] = 11
    travel[0][6] = 26
    travel[0][7] = 19
    travel[0][8] = 12
    
    travel[1][0] = 10
    travel[1][2] = 22
    travel[1][3] = 10
    travel[1][4] = 27
    travel[1][5] = 7
    travel[1][6] = 20
    travel[1][7] = 15
    travel[1][8] = 18
    
    travel[2][0] = 20
    travel[2][1] = 21
    travel[2][3] = 24
    travel[2][4] = 19
    travel[2][5] = 16
    travel[2][6] = 7
    travel[2][7] = 8
    travel[2][8] = 11
    
    travel[3][0] = 17
    travel[3][1] = 9
    travel[3][2] = 27
    travel[3][4] = 26
    travel[3][5] = 12
    travel[3][6] = 22
    travel[3][7] = 21
    travel[3][8] = 25
    
    travel[4][0] = 32
    travel[4][1] = 27
    travel[4][2] = 19
    travel[4][3] = 25
    travel[4][5] = 23
    travel[4][6] = 13
    travel[4][7] = 16
    travel[4][8] = 22
    
    travel[5][0] = 11
    travel[5][1] = 6
    travel[5][2] = 16
    travel[5][3] = 13
    travel[5][4] = 22
    travel[5][6] = 15
    travel[5][7] = 10
    travel[5][8] = 15
    
    travel[6][0] = 25
    travel[6][1] = 19
    travel[6][2] = 7
    travel[6][3] = 22
    travel[6][4] = 14
    travel[6][5] = 16
    travel[6][7] = 11
    travel[6][8] = 17
    
    travel[7][0] = 17
    travel[7][1] = 15
    travel[7][2] = 8
    travel[7][3] = 19
    travel[7][4] = 16
    travel[7][5] = 10
    travel[7][6] = 10
    travel[7][8] = 9
    
    travel[8][0] = 11
    travel[8][1] = 16
    travel[8][2] = 13
    travel[8][3] = 24
    travel[8][4] = 23
    travel[8][5] = 16
    travel[8][6] = 17
    travel[8][7] = 9

    # Friends data
    friends = [
        {'name': 'Amanda', 'location_name': 'Marina District', 'loc_index': 1, 
         'start': 14*60+45, 'end': 19*60+30, 'min_duration': 105},
        {'name': 'Melissa', 'location_name': 'The Castro', 'loc_index': 2, 
         'start': 9*60+30, 'end': 17*60+00, 'min_duration': 30},
        {'name': 'Jeffrey', 'location_name': 'Fisherman\'s Wharf', 'loc_index': 3, 
         'start': 12*60+45, 'end': 18*60+45, 'min_duration': 120},
        {'name': 'Matthew', 'location_name': 'Bayview', 'loc_index': 4, 
         'start': 10*60+15, 'end': 13*60+15, 'min_duration': 30},
        {'name': 'Nancy', 'location_name': 'Pacific Heights', 'loc_index': 5, 
         'start': 17*60+00, 'end': 21*60+30, 'min_duration': 105},
        {'name': 'Karen', 'location_name': 'Mission District', 'loc_index': 6, 
         'start': 17*60+30, 'end': 20*60+30, 'min_duration': 105},
        {'name': 'Robert', 'location_name': 'Alamo Square', 'loc_index': 7, 
         'start': 11*60+15, 'end': 17*60+30, 'min_duration': 120},
        {'name': 'Joseph', 'location_name': 'Golden Gate Park', 'loc_index': 8, 
         'start': 8*60+30, 'end': 21*60+15, 'min_duration': 105}
    ]

    # Convert minutes to time string (H:MM)
    def minutes_to_time(m):
        h = m // 60
        mm = m % 60
        return f"{h}:{mm:02d}"

    # DP setup
    memo = {}
    next_state = {}
    all_visited = (1 << 8) - 1

    def dp(loc, time, mask):
        if mask == all_visited:
            return 0
        key = (loc, time, mask)
        if key in memo:
            return memo[key]
        max_count = 0
        best_choice = None
        for j in range(8):
            if mask & (1 << j):
                continue
            f = friends[j]
            new_loc = f['loc_index']
            travel_dur = travel[loc][new_loc]
            arrival = time + travel_dur
            start_meeting = max(arrival, f['start'])
            if start_meeting + f['min_duration'] <= f['end']:
                end_meeting = start_meeting + f['min_duration']
                new_time = end_meeting
                new_mask = mask | (1 << j)
                count = 1 + dp(new_loc, new_time, new_mask)
                if count > max_count:
                    max_count = count
                    best_choice = (j, start_meeting, end_meeting, new_loc, new_time, new_mask)
        memo[key] = max_count
        if best_choice is not None:
            next_state[key] = best_choice
        return max_count

    # Start at Presidio (index 0) at 9:00 AM (540 minutes) with no meetings
    start_loc = 0
    start_time = 540
    start_mask = 0
    total_meetings = dp(start_loc, start_time, start_mask)

    # Backtrack to build itinerary
    itinerary = []
    state = (start_loc, start_time, start_mask)
    while state in next_state:
        j, start_meeting, end_meeting, new_loc, new_time, new_mask = next_state[state]
        f = friends[j]
        itinerary.append({
            'action': 'meet',
            'location': f['location_name'],
            'person': f['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        state = (new_loc, new_time, new_mask)

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()