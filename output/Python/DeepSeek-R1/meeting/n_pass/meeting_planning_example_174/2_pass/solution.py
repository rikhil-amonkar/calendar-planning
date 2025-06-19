import json

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Convert all times to minutes since midnight
    start_min = 9 * 60  # 9:00 AM

    # Kenneth's availability: 12:00 PM to 3:45 PM
    k_avail_start = 12 * 60
    k_avail_end = 15 * 60 + 45
    k_min_duration = 45  # min meeting time for Kenneth

    # Thomas's availability: 3:30 PM to 7:15 PM
    t_avail_start = 15 * 60 + 30
    t_avail_end = 19 * 60 + 15
    t_min_duration = 75  # min meeting time for Thomas

    # Travel times between locations (in minutes)
    travel_times = {
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Mission District', 'Pacific Heights'): 16,
        ('Pacific Heights', 'Mission District'): 15
    }

    # Try order: Kenneth (Mission District) then Thomas (Pacific Heights)
    k_start = min(k_avail_end - k_min_duration, 
                 t_avail_end - t_min_duration - travel_times[('Mission District', 'Pacific Heights')] - k_min_duration)
    k_start = max(k_avail_start, k_start)
    leave_nob = k_start - travel_times[('Nob Hill', 'Mission District')]
    if leave_nob >= start_min:
        k_end = k_start + k_min_duration
        t_arrive = k_end + travel_times[('Mission District', 'Pacific Heights')]
        t_start = max(t_avail_start, t_arrive)
        if t_start + t_min_duration <= t_avail_end:
            itinerary = [
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
                    "end_time": min_to_time(t_start + t_min_duration)
                }
            ]
            print(json.dumps({"itinerary": itinerary}))
            return

    # Try order: Thomas (Pacific Heights) then Kenneth (Mission District)
    t_start = min(t_avail_end - t_min_duration,
                 k_avail_end - k_min_duration - travel_times[('Pacific Heights', 'Mission District')] - t_min_duration)
    t_start = max(t_avail_start, t_start)
    leave_nob = t_start - travel_times[('Nob Hill', 'Pacific Heights')]
    if leave_nob >= start_min:
        t_end = t_start + t_min_duration
        k_arrive = t_end + travel_times[('Pacific Heights', 'Mission District')]
        k_start = max(k_avail_start, k_arrive)
        if k_start + k_min_duration <= k_avail_end:
            itinerary = [
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
                    "end_time": min_to_time(k_start + k_min_duration)
                }
            ]
            print(json.dumps({"itinerary": itinerary}))
            return

    # If both orders fail, try to meet one friend
    candidates = []

    # Try meeting Kenneth alone (at the latest possible time)
    k_start = k_avail_end - k_min_duration
    leave_nob = k_start - travel_times[('Nob Hill', 'Mission District')]
    if leave_nob >= start_min and k_start >= k_avail_start:
        candidates.append({
            "location": "Mission District",
            "person": "Kenneth",
            "start": k_start,
            "end": k_start + k_min_duration
        })

    # Try meeting Thomas alone (at the latest possible time)
    t_start = t_avail_end - t_min_duration
    leave_nob = t_start - travel_times[('Nob Hill', 'Pacific Heights')]
    if leave_nob >= start_min and t_start >= t_avail_start:
        candidates.append({
            "location": "Pacific Heights",
            "person": "Thomas",
            "start": t_start,
            "end": t_start + t_min_duration
        })

    # Choose the candidate with the earliest meeting start time
    if candidates:
        candidates.sort(key=lambda x: x['start'])
        best_candidate = candidates[0]
        itinerary = [
            {
                "action": "meet",
                "location": best_candidate['location'],
                "person": best_candidate['person'],
                "start_time": min_to_time(best_candidate['start']),
                "end_time": min_to_time(best_candidate['end'])
            }
        ]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()