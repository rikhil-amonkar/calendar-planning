import json
import math

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define the travel matrix
    locations = [
        "Sunset District",      #0
        "Russian Hill",         #1
        "The Castro",           #2
        "Richmond District",    #3
        "Marina District",      #4
        "North Beach",          #5
        "Union Square",         #6
        "Golden Gate Park"      #7
    ]
    
    travel_matrix = [[0] * 8 for _ in range(8)]
    
    # Fill the travel matrix with given times
    travel_data = {
        "Sunset District": {"Russian Hill": 24, "The Castro": 17, "Richmond District": 12, "Marina District": 21, "North Beach": 29, "Union Square": 30, "Golden Gate Park": 11},
        "Russian Hill": {"Sunset District": 23, "The Castro": 21, "Richmond District": 14, "Marina District": 7, "North Beach": 5, "Union Square": 11, "Golden Gate Park": 21},
        "The Castro": {"Sunset District": 17, "Russian Hill": 18, "Richmond District": 16, "Marina District": 21, "North Beach": 20, "Union Square": 19, "Golden Gate Park": 11},
        "Richmond District": {"Sunset District": 11, "Russian Hill": 13, "The Castro": 16, "Marina District": 9, "North Beach": 17, "Union Square": 21, "Golden Gate Park": 9},
        "Marina District": {"Sunset District": 19, "Russian Hill": 8, "The Castro": 22, "Richmond District": 11, "North Beach": 11, "Union Square": 16, "Golden Gate Park": 18},
        "North Beach": {"Sunset District": 27, "Russian Hill": 4, "The Castro": 22, "Richmond District": 18, "Marina District": 9, "Union Square": 7, "Golden Gate Park": 22},
        "Union Square": {"Sunset District": 26, "Russian Hill": 13, "The Castro": 19, "Richmond District": 20, "Marina District": 18, "North Beach": 10, "Golden Gate Park": 22},
        "Golden Gate Park": {"Sunset District": 10, "Russian Hill": 19, "The Castro": 13, "Richmond District": 7, "Marina District": 16, "North Beach": 24, "Union Square": 22}
    }
    
    for i, loc1 in enumerate(locations):
        for j, loc2 in enumerate(locations):
            if loc1 in travel_data and loc2 in travel_data[loc1]:
                travel_matrix[i][j] = travel_data[loc1][loc2]
    
    # Define friends data
    friends = [
        {"name": "Karen", "location": "Russian Hill", "start": time_to_minutes("20:45"), "end": time_to_minutes("21:45"), "min_duration": 60},
        {"name": "Jessica", "location": "The Castro", "start": time_to_minutes("15:45"), "end": time_to_minutes("19:30"), "min_duration": 60},
        {"name": "Matthew", "location": "Richmond District", "start": time_to_minutes("7:30"), "end": time_to_minutes("15:15"), "min_duration": 15},
        {"name": "Michelle", "location": "Marina District", "start": time_to_minutes("10:30"), "end": time_to_minutes("18:45"), "min_duration": 75},
        {"name": "Carol", "location": "North Beach", "start": time_to_minutes("12:00"), "end": time_to_minutes("17:00"), "min_duration": 90},
        {"name": "Stephanie", "location": "Union Square", "start": time_to_minutes("10:45"), "end": time_to_minutes("14:15"), "min_duration": 30},
        {"name": "Linda", "location": "Golden Gate Park", "start": time_to_minutes("10:45"), "end": time_to_minutes("22:00"), "min_duration": 90}
    ]
    
    # Map friend locations to indices
    loc_to_index = {loc: idx for idx, loc in enumerate(locations)}
    
    # Precompute friend indices and their location indices
    for friend in friends:
        friend['loc_index'] = loc_to_index[friend['location']]
    
    n = len(friends)
    num_states = 1 << n
    INF = 10**9
    
    # Initialize DP table: [state][location] -> (finish_time, itinerary)
    dp = [[(INF, []) for _ in range(8)] for _ in range(num_states)]
    start_loc = 0  # Sunset District
    start_time = time_to_minutes("9:00")
    dp[0][start_loc] = (start_time, [])
    
    # DP iteration
    for state in range(num_states):
        for loc in range(8):
            current_time, itinerary = dp[state][loc]
            if current_time == INF:
                continue
            for idx, friend in enumerate(friends):
                if state & (1 << idx):
                    continue
                next_loc = friend['loc_index']
                travel_time = travel_matrix[loc][next_loc]
                arrival_time = current_time + travel_time
                start_meeting = max(arrival_time, friend['start'])
                end_meeting = start_meeting + friend['min_duration']
                if end_meeting > friend['end']:
                    continue
                new_state = state | (1 << idx)
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_meeting),
                    "end_time": minutes_to_time(end_meeting)
                }]
                if end_meeting < dp[new_state][next_loc][0]:
                    dp[new_state][next_loc] = (end_meeting, new_itinerary)
    
    # Find the best state with most meetings
    best_state = None
    max_meetings = -1
    best_itinerary = []
    for state in range(num_states):
        count = bin(state).count('1')
        for loc in range(8):
            finish_time, itinerary = dp[state][loc]
            if finish_time < INF and count > max_meetings:
                max_meetings = count
                best_state = state
                best_itinerary = itinerary
    
    # Output the result as JSON
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()