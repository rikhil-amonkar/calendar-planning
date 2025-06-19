import json

def main():
    # Define the travel matrix as a dictionary of dictionaries
    travel_matrix = {
        "Russian Hill": {
            "Presidio": 14,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "Richmond District": 14,
            "Fisherman's Wharf": 7,
            "Golden Gate Park": 21,
            "Bayview": 23
        },
        "Presidio": {
            "Russian Hill": 14,
            "Chinatown": 21,
            "Pacific Heights": 11,
            "Richmond District": 7,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Chinatown": {
            "Russian Hill": 7,
            "Presidio": 21,
            "Pacific Heights": 10,
            "Richmond District": 20,
            "Fisherman's Wharf": 8,
            "Golden Gate Park": 23,
            "Bayview": 22
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "Presidio": 11,
            "Chinatown": 11,
            "Richmond District": 12,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15,
            "Bayview": 22
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Presidio": 7,
            "Chinatown": 20,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 18,
            "Golden Gate Park": 9,
            "Bayview": 26
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "Richmond District": 18,
            "Golden Gate Park": 25,
            "Bayview": 26
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16,
            "Richmond District": 7,
            "Fisherman's Wharf": 24,
            "Bayview": 23
        },
        "Bayview": {
            "Russian Hill": 23,
            "Presidio": 31,
            "Chinatown": 18,
            "Pacific Heights": 23,
            "Richmond District": 25,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        }
    }
    
    # Define the friends with their constraints (time in minutes)
    friends = [
        {"name": "Matthew", "location": "Presidio", "start": 11*60, "end": 21*60, "min_duration": 90},
        {"name": "Margaret", "location": "Chinatown", "start": 9*60+15, "end": 18*60+45, "min_duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "start": 14*60+15, "end": 17*60, "min_duration": 15},
        {"name": "Helen", "location": "Richmond District", "start": 19*60+45, "end": 22*60, "min_duration": 60},
        {"name": "Rebecca", "location": "Fisherman's Wharf", "start": 21*60+15, "end": 22*60+15, "min_duration": 60},
        {"name": "Kimberly", "location": "Golden Gate Park", "start": 13*60, "end": 16*60+30, "min_duration": 120},
        {"name": "Kenneth", "location": "Bayview", "start": 14*60+30, "end": 18*60, "min_duration": 60}
    ]
    
    # Helper function to convert minutes to time string (H:MM)
    def minutes_to_time(mins):
        h = mins // 60
        m = mins % 60
        return f"{h}:{m:02d}"
    
    # Memoization dictionary for DFS states
    memo = {}
    
    # DFS function with memoization
    def dfs(current_time, current_location, unscheduled):
        key = (current_time, current_location, unscheduled)
        if key in memo:
            return memo[key]
        
        best_count = 0
        best_itinerary = []
        
        # If no more friends to schedule, return empty itinerary
        if not unscheduled:
            return (0, [])
        
        # Try to schedule each unscheduled friend
        for idx in sorted(unscheduled):
            friend = friends[idx]
            loc = friend['location']
            
            # Get travel time
            if current_location == loc:
                travel_time = 0
            else:
                travel_time = travel_matrix[current_location][loc]
            
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['min_duration']
            
            # Check if meeting is feasible
            if meeting_end <= friend['end']:
                # Create meeting event
                meeting_event = {
                    "action": "meet",
                    "location": loc,
                    "person": friend['name'],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                }
                new_unscheduled = unscheduled - {idx}
                # Recurse to schedule the remaining friends
                count_rest, itinerary_rest = dfs(meeting_end, loc, new_unscheduled)
                total_count = 1 + count_rest
                # Update best if we found a better count
                if total_count > best_count:
                    best_count = total_count
                    best_itinerary = [meeting_event] + itinerary_rest
        
        memo[key] = (best_count, best_itinerary)
        return (best_count, best_itinerary)
    
    # Initial state: start at Russian Hill at 9:00 AM (540 minutes) with all friends unscheduled
    start_time = 540
    start_location = "Russian Hill"
    unscheduled = frozenset(range(len(friends)))
    count, itinerary = dfs(start_time, start_location, unscheduled)
    
    # Format the result as JSON
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()