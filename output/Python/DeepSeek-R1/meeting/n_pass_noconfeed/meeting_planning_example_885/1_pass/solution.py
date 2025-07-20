import json

def main():
    # Convert time string to minutes
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minutes = int(parts[1][:2])
        if time_str.endswith('PM') and hour != 12:
            hour += 12
        if time_str.endswith('AM') and hour == 12:
            hour = 0
        return hour * 60 + minutes

    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Travel matrix: 10x10
    locations = [
        'Russian Hill',          # 0
        'Marina District',        # 1
        'Financial District',     # 2
        'Alamo Square',           # 3
        'Golden Gate Park',       # 4
        'The Castro',             # 5
        'Bayview',                # 6
        'Sunset District',        # 7
        'Haight-Ashbury',         # 8
        'Nob Hill'                # 9
    ]
    
    travel_matrix = [
        [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],
        [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],
        [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],
        [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],
        [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],
        [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],
        [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],
        [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],
        [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],
        [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]
    ]
    
    # Meetings data: person, location, available time, min duration
    meetings = [
        {'person': 'Mark', 'location': 'Marina District', 'loc_index': 1, 
         'start': time_to_minutes('6:45PM'), 'end': time_to_minutes('9:00PM'), 'duration': 90},
        {'person': 'Karen', 'location': 'Financial District', 'loc_index': 2, 
         'start': time_to_minutes('9:30AM'), 'end': time_to_minutes('12:45PM'), 'duration': 90},
        {'person': 'Barbara', 'location': 'Alamo Square', 'loc_index': 3, 
         'start': time_to_minutes('10:00AM'), 'end': time_to_minutes('7:30PM'), 'duration': 90},
        {'person': 'Nancy', 'location': 'Golden Gate Park', 'loc_index': 4, 
         'start': time_to_minutes('4:45PM'), 'end': time_to_minutes('8:00PM'), 'duration': 105},
        {'person': 'David', 'location': 'The Castro', 'loc_index': 5, 
         'start': time_to_minutes('9:00AM'), 'end': time_to_minutes('6:00PM'), 'duration': 120},
        {'person': 'Linda', 'location': 'Bayview', 'loc_index': 6, 
         'start': time_to_minutes('6:15PM'), 'end': time_to_minutes('7:45PM'), 'duration': 45},
        {'person': 'Kevin', 'location': 'Sunset District', 'loc_index': 7, 
         'start': time_to_minutes('10:00AM'), 'end': time_to_minutes('5:45PM'), 'duration': 120},
        {'person': 'Matthew', 'location': 'Haight-Ashbury', 'loc_index': 8, 
         'start': time_to_minutes('10:15AM'), 'end': time_to_minutes('3:30PM'), 'duration': 45},
        {'person': 'Andrew', 'location': 'Nob Hill', 'loc_index': 9, 
         'start': time_to_minutes('11:45AM'), 'end': time_to_minutes('4:45PM'), 'duration': 105}
    ]
    
    n = len(meetings)  # 9 meetings
    dp = [[None] * n for _ in range(1 << n)]
    parent_mask = [[None] * n for _ in range(1 << n)]
    parent_index = [[None] * n for _ in range(1 << n)]
    meeting_start = [[None] * n for _ in range(1 << n)]
    meeting_end = [[None] * n for _ in range(1 << n)]
    
    # Start at Russian Hill (0) at 9:00 AM (540 minutes)
    start_time = time_to_minutes('9:00AM')  # 540 minutes
    
    # Initialize DP: from start to each meeting
    for i in range(n):
        loc_idx = meetings[i]['loc_index']
        travel_time = travel_matrix[0][loc_idx]
        arrive_time = start_time + travel_time
        start_meet = max(arrive_time, meetings[i]['start'])
        end_meet = start_meet + meetings[i]['duration']
        if end_meet <= meetings[i]['end']:
            mask = 1 << i
            dp[mask][i] = end_meet
            meeting_start[mask][i] = start_meet
            meeting_end[mask][i] = end_meet
            parent_mask[mask][i] = None
            parent_index[mask][i] = None
    
    # DP over all masks
    for mask in range(1 << n):
        for i in range(n):
            if dp[mask][i] is None:
                continue
            for j in range(n):
                if mask & (1 << j):
                    continue
                from_loc = meetings[i]['loc_index']
                to_loc = meetings[j]['loc_index']
                travel_time = travel_matrix[from_loc][to_loc]
                arrive_next = dp[mask][i] + travel_time
                start_next = max(arrive_next, meetings[j]['start'])
                end_next = start_next + meetings[j]['duration']
                if end_next <= meetings[j]['end']:
                    new_mask = mask | (1 << j)
                    if dp[new_mask][j] is None or end_next < dp[new_mask][j]:
                        dp[new_mask][j] = end_next
                        parent_mask[new_mask][j] = mask
                        parent_index[new_mask][j] = i
                        meeting_start[new_mask][j] = start_next
                        meeting_end[new_mask][j] = end_next
    
    # Find the best state: max meetings, and if tie then earliest end time
    best_mask = None
    best_index = None
    best_count = -1
    best_end = float('inf')
    
    for mask in range(1 << n):
        for i in range(n):
            if dp[mask][i] is not None:
                count = bin(mask).count('1')
                if count > best_count or (count == best_count and dp[mask][i] < best_end):
                    best_count = count
                    best_mask = mask
                    best_index = i
                    best_end = dp[mask][i]
    
    # Backtrack to get the schedule
    schedule = []
    current_mask = best_mask
    current_index = best_index
    
    while current_mask is not None and current_index is not None:
        start_time_here = meeting_start[current_mask][current_index]
        end_time_here = meeting_end[current_mask][current_index]
        person = meetings[current_index]['person']
        location = meetings[current_index]['location']
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(start_time_here),
            'end_time': minutes_to_time(end_time_here)
        })
        
        prev_mask = parent_mask[current_mask][current_index]
        prev_index = parent_index[current_mask][current_index]
        current_mask = prev_mask
        current_index = prev_index
    
    # Reverse to get chronological order
    schedule.reverse()
    
    # Output as JSON
    result = {
        'itinerary': schedule
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()