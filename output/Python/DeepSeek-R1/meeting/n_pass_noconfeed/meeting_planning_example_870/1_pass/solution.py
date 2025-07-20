import json

def format_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def main():
    # Define travel times dictionary
    travel_times = {
        "Pacific Heights": {
            "Marina District": 6,
            "The Castro": 16,
            "Richmond District": 12,
            "Alamo Square": 10,
            "Financial District": 13,
            "Presidio": 11,
            "Mission District": 15,
            "Nob Hill": 8,
            "Russian Hill": 7
        },
        "Marina District": {
            "Pacific Heights": 7,
            "The Castro": 22,
            "Richmond District": 11,
            "Alamo Square": 15,
            "Financial District": 17,
            "Presidio": 10,
            "Mission District": 20,
            "Nob Hill": 12,
            "Russian Hill": 8
        },
        "The Castro": {
            "Pacific Heights": 16,
            "Marina District": 21,
            "Richmond District": 16,
            "Alamo Square": 8,
            "Financial District": 21,
            "Presidio": 20,
            "Mission District": 7,
            "Nob Hill": 16,
            "Russian Hill": 18
        },
        "Richmond District": {
            "Pacific Heights": 10,
            "Marina District": 9,
            "The Castro": 16,
            "Alamo Square": 13,
            "Financial District": 22,
            "Presidio": 7,
            "Mission District": 20,
            "Nob Hill": 17,
            "Russian Hill": 13
        },
        "Alamo Square": {
            "Pacific Heights": 10,
            "Marina District": 15,
            "The Castro": 8,
            "Richmond District": 11,
            "Financial District": 17,
            "Presidio": 17,
            "Mission District": 10,
            "Nob Hill": 11,
            "Russian Hill": 13
        },
        "Financial District": {
            "Pacific Heights": 13,
            "Marina District": 15,
            "The Castro": 20,
            "Richmond District": 21,
            "Alamo Square": 17,
            "Presidio": 22,
            "Mission District": 17,
            "Nob Hill": 8,
            "Russian Hill": 11
        },
        "Presidio": {
            "Pacific Heights": 11,
            "Marina District": 11,
            "The Castro": 21,
            "Richmond District": 7,
            "Alamo Square": 19,
            "Financial District": 23,
            "Mission District": 26,
            "Nob Hill": 18,
            "Russian Hill": 14
        },
        "Mission District": {
            "Pacific Heights": 16,
            "Marina District": 19,
            "The Castro": 7,
            "Richmond District": 20,
            "Alamo Square": 11,
            "Financial District": 15,
            "Presidio": 25,
            "Nob Hill": 12,
            "Russian Hill": 15
        },
        "Nob Hill": {
            "Pacific Heights": 8,
            "Marina District": 11,
            "The Castro": 17,
            "Richmond District": 14,
            "Alamo Square": 11,
            "Financial District": 9,
            "Presidio": 17,
            "Mission District": 13,
            "Russian Hill": 5
        },
        "Russian Hill": {
            "Pacific Heights": 7,
            "Marina District": 7,
            "The Castro": 21,
            "Richmond District": 14,
            "Alamo Square": 15,
            "Financial District": 11,
            "Presidio": 14,
            "Mission District": 16,
            "Nob Hill": 5
        }
    }
    
    # Define friends with their constraints
    friends = [
        {"name": "Linda", "location": "Marina District", "start": 18*60, "end": 22*60, "duration": 30},
        {"name": "Kenneth", "location": "The Castro", "start": 14*60+45, "end": 16*60+15, "duration": 30},
        {"name": "Kimberly", "location": "Richmond District", "start": 14*60+15, "end": 22*60, "duration": 30},
        {"name": "Paul", "location": "Alamo Square", "start": 21*60, "end": 21*60+30, "duration": 15},
        {"name": "Carol", "location": "Financial District", "start": 10*60+15, "end": 12*60, "duration": 60},
        {"name": "Brian", "location": "Presidio", "start": 10*60, "end": 21*60+30, "duration": 75},
        {"name": "Laura", "location": "Mission District", "start": 16*60+15, "end": 20*60+30, "duration": 30},
        {"name": "Sandra", "location": "Nob Hill", "start": 9*60+15, "end": 18*60+30, "duration": 60},
        {"name": "Karen", "location": "Russian Hill", "start": 18*60+30, "end": 22*60, "duration": 75}
    ]
    
    n = len(friends)
    INF = 10**9
    dp = [[INF] * n for _ in range(1 << n)]
    parent = [[None] * n for _ in range(1 << n)]  # (prev_mask, prev_index, start_time, end_time)
    
    # Initialize for meetings from start
    for i in range(n):
        loc = friends[i]["location"]
        travel_time = travel_times["Pacific Heights"][loc]
        arrival_time = 540 + travel_time
        start_meet = max(arrival_time, friends[i]["start"])
        end_meet = start_meet + friends[i]["duration"]
        if end_meet <= friends[i]["end"]:
            mask = 1 << i
            dp[mask][i] = end_meet
            parent[mask][i] = (-1, -1, start_meet, end_meet)
    
    # DP for state (mask, i)
    for mask in range(1 << n):
        for i in range(n):
            if (mask & (1 << i)) == 0 or dp[mask][i] == INF:
                continue
            for j in range(n):
                if mask & (1 << j):
                    continue
                from_loc = friends[i]["location"]
                to_loc = friends[j]["location"]
                travel_time = travel_times[from_loc][to_loc]
                arrival_time = dp[mask][i] + travel_time
                start_meet = max(arrival_time, friends[j]["start"])
                end_meet = start_meet + friends[j]["duration"]
                if end_meet <= friends[j]["end"]:
                    new_mask = mask | (1 << j)
                    if end_meet < dp[new_mask][j]:
                        dp[new_mask][j] = end_meet
                        parent[new_mask][j] = (mask, i, start_meet, end_meet)
    
    # Find best solution (max count, then min finish time)
    best_count = 0
    best_mask = None
    best_index = None
    best_time = INF
    
    for mask in range(1 << n):
        count = bin(mask).count("1")
        for i in range(n):
            if dp[mask][i] < INF:
                if count > best_count:
                    best_count = count
                    best_mask = mask
                    best_index = i
                    best_time = dp[mask][i]
                elif count == best_count and dp[mask][i] < best_time:
                    best_mask = mask
                    best_index = i
                    best_time = dp[mask][i]
    
    # Reconstruct itinerary
    itinerary = []
    if best_count > 0:
        current_mask = best_mask
        current_index = best_index
        while current_mask != 0:
            prev_mask, prev_index, start_meet, end_meet = parent[current_mask][current_index]
            itinerary.append({
                "action": "meet",
                "location": friends[current_index]["location"],
                "person": friends[current_index]["name"],
                "start_time": format_time(start_meet),
                "end_time": format_time(end_meet)
            })
            current_mask = prev_mask
            current_index = prev_index
            if current_mask == -1:
                break
        itinerary.reverse()
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()