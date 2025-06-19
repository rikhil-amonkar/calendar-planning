import json

def main():
    travel_times = {
        "Embarcadero": {
            "Bayview": 21,
            "Chinatown": 7,
            "Alamo Square": 19,
            "Nob Hill": 10,
            "Union Square": 10,
            "The Castro": 25,
            "North Beach": 5,
            "Fisherman's Wharf": 6,
            "Marina District": 12
        },
        "Bayview": {
            "Embarcadero": 19,
            "Chinatown": 19,
            "Alamo Square": 16,
            "Nob Hill": 20,
            "Union Square": 18,
            "The Castro": 19,
            "North Beach": 22,
            "Fisherman's Wharf": 25,
            "Marina District": 27
        },
        "Chinatown": {
            "Embarcadero": 5,
            "Bayview": 20,
            "Alamo Square": 17,
            "Nob Hill": 9,
            "Union Square": 7,
            "The Castro": 22,
            "North Beach": 3,
            "Fisherman's Wharf": 8,
            "Marina District": 12
        },
        "Alamo Square": {
            "Embarcadero": 16,
            "Bayview": 16,
            "Chinatown": 15,
            "Nob Hill": 11,
            "Union Square": 14,
            "The Castro": 8,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Marina District": 15
        },
        "Nob Hill": {
            "Embarcadero": 9,
            "Bayview": 19,
            "Chinatown": 6,
            "Alamo Square": 11,
            "Union Square": 7,
            "The Castro": 17,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Marina District": 11
        },
        "Union Square": {
            "Embarcadero": 11,
            "Bayview": 15,
            "Chinatown": 7,
            "Alamo Square": 15,
            "Nob Hill": 9,
            "The Castro": 17,
            "North Beach": 10,
            "Fisherman's Wharf": 15,
            "Marina District": 18
        },
        "The Castro": {
            "Embarcadero": 22,
            "Bayview": 19,
            "Chinatown": 22,
            "Alamo Square": 8,
            "Nob Hill": 16,
            "Union Square": 19,
            "North Beach": 20,
            "Fisherman's Wharf": 24,
            "Marina District": 21
        },
        "North Beach": {
            "Embarcadero": 6,
            "Bayview": 25,
            "Chinatown": 6,
            "Alamo Square": 16,
            "Nob Hill": 7,
            "Union Square": 7,
            "The Castro": 23,
            "Fisherman's Wharf": 5,
            "Marina District": 9
        },
        "Fisherman's Wharf": {
            "Embarcadero": 8,
            "Bayview": 26,
            "Chinatown": 12,
            "Alamo Square": 21,
            "Nob Hill": 11,
            "Union Square": 13,
            "The Castro": 27,
            "North Beach": 6,
            "Marina District": 9
        },
        "Marina District": {
            "Embarcadero": 14,
            "Bayview": 27,
            "Chinatown": 15,
            "Alamo Square": 15,
            "Nob Hill": 12,
            "Union Square": 16,
            "The Castro": 22,
            "North Beach": 11,
            "Fisherman's Wharf": 10
        }
    }
    
    friends = [
        ("Matthew", "Bayview", 19*60+15, 22*60, 120),
        ("Karen", "Chinatown", 19*60+15, 21*60+15, 90),
        ("Sarah", "Alamo Square", 20*60, 21*60+45, 105),
        ("Jessica", "Nob Hill", 16*60+30, 18*60+45, 120),
        ("Mary", "Union Square", 16*60+45, 21*60+30, 60),
        ("Charles", "The Castro", 16*60+30, 22*60, 105),
        ("Nancy", "North Beach", 14*60+45, 20*60, 15),
        ("Thomas", "Fisherman's Wharf", 13*60+30, 19*60, 30),
        ("Brian", "Marina District", 12*60+15, 18*60, 60)
    ]
    
    our_locations = list(travel_times.keys())
    n = len(friends)
    dp = {}
    parent = {}
    start_time = 9 * 60
    dp[(0, "Embarcadero")] = start_time
    parent[(0, "Embarcadero")] = None
    
    total_states = 1 << n
    for state in range(total_states):
        for loc in our_locations:
            key = (state, loc)
            if key not in dp:
                continue
            current_time = dp[key]
            for i in range(n):
                if state & (1 << i):
                    continue
                f_name, f_loc, f_start_min, f_end_min, f_duration = friends[i]
                if f_loc not in travel_times[loc]:
                    continue
                travel_duration = travel_times[loc][f_loc]
                arrival_time = current_time + travel_duration
                meeting_start = max(arrival_time, f_start_min)
                meeting_end = meeting_start + f_duration
                if meeting_end > f_end_min:
                    continue
                new_state = state | (1 << i)
                new_key = (new_state, f_loc)
                if new_key not in dp or meeting_end < dp[new_key]:
                    dp[new_key] = meeting_end
                    parent[new_key] = (state, loc, i, meeting_start, meeting_end)
    
    best_state = None
    best_loc = None
    best_count = -1
    for (state, loc), end_time in dp.items():
        count = bin(state).count("1")
        if count > best_count:
            best_count = count
            best_state = state
            best_loc = loc
    
    meetings = []
    current_key = (best_state, best_loc)
    while current_key in parent and parent[current_key] is not None:
        state, loc, i, start, end = parent[current_key]
        f_name = friends[i][0]
        f_loc = friends[i][1]
        meetings.append((f_name, f_loc, start, end))
        current_key = (state, loc)
    meetings.reverse()
    
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    itinerary_list = []
    for meet in meetings:
        name, loc, start, end = meet
        itinerary_list.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    
    result = {
        "itinerary": itinerary_list
    }
    print(json.dumps(result))

if __name__ == '__main__':
    main()