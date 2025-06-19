import json

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    start_available = 9 * 60   # 9:00 AM in minutes

    k_avail_start = 12 * 60    # 12:00
    k_avail_end = 15 * 60 + 45 # 15:45
    k_duration = 45            # min meeting time for Kenneth

    t_avail_start = 15 * 60 + 30 # 15:30
    t_avail_end = 19 * 60 + 15   # 19:15 (7:15 PM)
    t_duration = 75               # min meeting time for Thomas

    travel_Nob_to_Mission = 13
    travel_Nob_to_Pacific = 8
    travel_Mission_to_Pacific = 16
    travel_Pacific_to_Mission = 15

    candidates = []

    # Option 1: Kenneth then Thomas
    k_start = max(k_avail_start, start_available + travel_Nob_to_Mission)
    k_end = k_start + k_duration
    if k_end <= k_avail_end:
        t_arrive = k_end + travel_Mission_to_Pacific
        t_start = max(t_avail_start, t_arrive)
        t_end = t_start + t_duration
        if t_end <= t_avail_end:
            candidates.append({
                'first_start': k_start,
                'itinerary': [
                    {
                        "action": "meet",
                        "location": "Mission District",
                        "person": "Kenneth",
                        "start_time": min_to_time(k_start),
                        "end_time": min_to_time(k_end)
                    },
                    {
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Thomas",
                        "start_time": min_to_time(t_start),
                        "end_time": min_to_time(t_end)
                    }
                ]
            })
    
    # Option 2: Thomas then Kenneth
    t_start = max(t_avail_start, start_available + travel_Nob_to_Pacific)
    t_end = t_start + t_duration
    if t_end <= t_avail_end:
        k_arrive = t_end + travel_Pacific_to_Mission
        k_start = max(k_avail_start, k_arrive)
        k_end = k_start + k_duration
        if k_end <= k_avail_end:
            candidates.append({
                'first_start': t_start,
                'itinerary': [
                    {
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Thomas",
                        "start_time": min_to_time(t_start),
                        "end_time": min_to_time(t_end)
                    },
                    {
                        "action": "meet",
                        "location": "Mission District",
                        "person": "Kenneth",
                        "start_time": min_to_time(k_start),
                        "end_time": min_to_time(k_end)
                    }
                ]
            })
    
    if candidates:
        candidates.sort(key=lambda x: x['first_start'])
        best_candidate = candidates[0]
        print(json.dumps({"itinerary": best_candidate['itinerary']}))
    else:
        # Try to meet one friend
        one_candidate = []
        # Kenneth alone
        k_start = max(k_avail_start, start_available + travel_Nob_to_Mission)
        k_end = k_start + k_duration
        if k_end <= k_avail_end:
            one_candidate.append({
                'start': k_start,
                'itinerary': [
                    {
                        "action": "meet",
                        "location": "Mission District",
                        "person": "Kenneth",
                        "start_time": min_to_time(k_start),
                        "end_time": min_to_time(k_end)
                    }
                ]
            })
        
        # Thomas alone
        t_start = max(t_avail_start, start_available + travel_Nob_to_Pacific)
        t_end = t_start + t_duration
        if t_end <= t_avail_end:
            one_candidate.append({
                'start': t_start,
                'itinerary': [
                    {
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Thomas",
                        "start_time": min_to_time(t_start),
                        "end_time": min_to_time(t_end)
                    }
                ]
            })
        
        if one_candidate:
            one_candidate.sort(key=lambda x: x['start'])
            print(json.dumps({"itinerary": one_candidate[0]['itinerary']}))
        else:
            print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()