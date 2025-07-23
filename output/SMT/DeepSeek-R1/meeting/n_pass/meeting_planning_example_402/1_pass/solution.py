import itertools

def main():
    meetings = [
        {"name": "Matthew", "loc": "Marina District", "window": [15, 165], "duration": 15},
        {"name": "Joseph", "loc": "Financial District", "window": [315, 555], "duration": 30},
        {"name": "Robert", "loc": "Union Square", "window": [75, 750], "duration": 15},
        {"name": "Patricia", "loc": "Sunset District", "window": [480, 600], "duration": 45},
        {"name": "Sarah", "loc": "Haight-Ashbury", "window": [480, 645], "duration": 105}
    ]
    
    travel_times = {
        "Golden Gate Park": {
            "Golden Gate Park": 0,
            "Haight-Ashbury": 7,
            "Sunset District": 10,
            "Marina District": 16,
            "Financial District": 26,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Haight-Ashbury": 0,
            "Sunset District": 15,
            "Marina District": 17,
            "Financial District": 21,
            "Union Square": 17
        },
        "Sunset District": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 15,
            "Sunset District": 0,
            "Marina District": 21,
            "Financial District": 30,
            "Union Square": 30
        },
        "Marina District": {
            "Golden Gate Park": 18,
            "Haight-Ashbury": 16,
            "Sunset District": 19,
            "Marina District": 0,
            "Financial District": 17,
            "Union Square": 16
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Sunset District": 31,
            "Marina District": 15,
            "Financial District": 0,
            "Union Square": 9
        },
        "Union Square": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Sunset District": 26,
            "Marina District": 18,
            "Financial District": 9,
            "Union Square": 0
        }
    }
    
    n = len(meetings)
    all_meetings = list(range(n))
    base_hour = 9
    
    for k in range(n, 0, -1):
        for subset in itertools.combinations(all_meetings, k):
            for perm in itertools.permutations(subset):
                current_time = 0
                current_loc = "Golden Gate Park"
                schedule = []
                feasible = True
                for idx in perm:
                    m = meetings[idx]
                    travel = travel_times[current_loc][m['loc']]
                    arrive_time = current_time + travel
                    start_time = max(arrive_time, m['window'][0])
                    if start_time > m['window'][1]:
                        feasible = False
                        break
                    end_time = start_time + m['duration']
                    schedule.append((idx, start_time, end_time))
                    current_time = end_time
                    current_loc = m['loc']
                if feasible:
                    itinerary = []
                    for (idx, start, end) in schedule:
                        hour_start = base_hour + start // 60
                        minute_start = start % 60
                        start_str = f"{hour_start:02d}:{minute_start:02d}"
                        hour_end = base_hour + end // 60
                        minute_end = end % 60
                        end_str = f"{hour_end:02d}:{minute_end:02d}"
                        itinerary.append({
                            "action": "meet",
                            "person": meetings[idx]['name'],
                            "start_time": start_str,
                            "end_time": end_str
                        })
                    result = {"itinerary": itinerary}
                    print("SOLUTION:", result)
                    return
    result = {"itinerary": []}
    print("SOLUTION:", result)

if __name__ == '__main__':
    main()