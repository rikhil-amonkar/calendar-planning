import json

def time_to_minutes(time_str):
    s = time_str.strip()
    if s.endswith("AM"):
        s = s.replace("AM", "").strip()
        base = 0
    elif s.endswith("PM"):
        s = s.replace("PM", "").strip()
        base = 12
    else:
        base = 0

    parts = s.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if base == 12 and hour != 12:
        hour += 12
    if base == 0 and hour == 12:
        hour = 0
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    period = "AM"
    if hours >= 12:
        period = "PM"
        if hours > 12:
            hours -= 12
    if hours == 0:
        hours = 12
    return f"{hours}:{mins:02d}{period}"

travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Bayview": 19,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
        "The Castro": 20,
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Sunset District": 30
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Presidio": 17,
        "Bayview": 26,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "The Castro": 27,
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Sunset District": 27
    },
    "Presidio": {
        "Financial District": 23,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
        "The Castro": 21,
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Sunset District": 15
    },
    "Bayview": {
        "Financial District": 19,
        "Fisherman's Wharf": 25,
        "Presidio": 32,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 21,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Bayview": 18,
        "Russian Hill": 17,
        "The Castro": 6,
        "Marina District": 17,
        "Richmond District": 10,
        "Union Square": 19,
        "Sunset District": 15
    },
    "Russian Hill": {
        "Financial District": 11,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Bayview": 23,
        "Haight-Ashbury": 17,
        "The Castro": 21,
        "Marina District": 7,
        "Richmond District": 14,
        "Union Square": 10,
        "Sunset District": 23
    },
    "The Castro": {
        "Financial District": 21,
        "Fisherman's Wharf": 24,
        "Presidio": 20,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Bayview": 27,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "Union Square": 16,
        "Sunset District": 19
    },
    "Richmond District": {
        "Financial District": 22,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Bayview": 15,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
        "The Castro": 17,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 30
    }
}

friends = [
    {"name": "Mark", "location": "Fisherman's Wharf", "start": time_to_minutes("8:15AM"), "end": time_to_minutes("10:00AM"), "min_duration": 30},
    {"name": "Stephanie", "location": "Presidio", "start": time_to_minutes("12:15PM"), "end": time_to_minutes("3:00PM"), "min_duration": 75},
    {"name": "Betty", "location": "Bayview", "start": time_to_minutes("7:15AM"), "end": time_to_minutes("8:30PM"), "min_duration": 15},
    {"name": "Lisa", "location": "Haight-Ashbury", "start": time_to_minutes("3:30PM"), "end": time_to_minutes("6:30PM"), "min_duration": 45},
    {"name": "William", "location": "Russian Hill", "start": time_to_minutes("6:45PM"), "end": time_to_minutes("8:00PM"), "min_duration": 60},
    {"name": "Brian", "location": "The Castro", "start": time_to_minutes("9:15AM"), "end": time_to_minutes("1:15PM"), "min_duration": 30},
    {"name": "Joseph", "location": "Marina District", "start": time_to_minutes("10:45AM"), "end": time_to_minutes("3:00PM"), "min_duration": 90},
    {"name": "Ashley", "location": "Richmond District", "start": time_to_minutes("9:45AM"), "end": time_to_minutes("11:15AM"), "min_duration": 45},
    {"name": "Patricia", "location": "Union Square", "start": time_to_minutes("4:30PM"), "end": time_to_minutes("8:00PM"), "min_duration": 120},
    {"name": "Karen", "location": "Sunset District", "start": time_to_minutes("4:30PM"), "end": time_to_minutes("10:00PM"), "min_duration": 105}
]

def main():
    n = len(friends)
    num_masks = 1 << n
    # dp[mask] is a dictionary: key: location, value: (time, parent_info)
    dp = [dict() for _ in range(num_masks)]
    start_loc = "Financial District"
    start_time = time_to_minutes("9:00AM")
    dp[0][start_loc] = (start_time, None)  # None for parent info for the start state
    
    # parent: key = (mask, location), value = (prev_mask, prev_loc, friend_index)
    parent = {}
    
    for mask in range(num_masks):
        for loc, (time, _) in dp[mask].items():
            for i in range(n):
                if mask & (1 << i):
                    continue
                friend = friends[i]
                next_loc = friend['location']
                try:
                    tt = travel_times[loc][next_loc]
                except KeyError:
                    continue
                arrival = time + tt
                start_meeting = max(arrival, friend['start'])
                end_meeting = start_meeting + friend['min_duration']
                if end_meeting > friend['end']:
                    continue
                new_mask = mask | (1 << i)
                if next_loc not in dp[new_mask] or end_meeting < dp[new_mask].get(next_loc, (float('inf'),))[0]:
                    dp[new_mask][next_loc] = (end_meeting, (mask, loc))
                    parent[(new_mask, next_loc)] = (mask, loc, i)
    
    best_mask = 0
    best_count = 0
    best_time = None
    best_loc = None
    for mask in range(num_masks):
        count = bin(mask).count("1")
        for loc, (time, _) in dp[mask].items():
            if count > best_count or (count == best_count and (best_time is None or time < best_time)):
                best_count = count
                best_mask = mask
                best_loc = loc
                best_time = time
                
    itinerary = []
    if best_count > 0:
        current_mask = best_mask
        current_loc = best_loc
        meetings = []
        while current_mask != 0:
            if (current_mask, current_loc) not in parent:
                break
            prev_mask, prev_loc, i = parent[(current_mask, current_loc)]
            friend = friends[i]
            # The state (current_mask, current_loc) has time = best_time (which is the end time of the meeting)
            start_meeting = best_time - friend['min_duration']
            meetings.append({
                "action": "meet",
                "location": current_loc,
                "person": friend['name'],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(best_time)
            })
            current_mask = prev_mask
            current_loc = prev_loc
            best_time = dp[current_mask][current_loc][0]
        meetings.reverse()
        itinerary = meetings
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()