import heapq
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    locations = [
        "Bayview",
        "North Beach",
        "Fisherman's Wharf",
        "Haight-Ashbury",
        "Nob Hill",
        "Golden Gate Park",
        "Union Square",
        "Alamo Square",
        "Presidio",
        "Chinatown",
        "Pacific Heights"
    ]
    travel_times = {
        "Bayview": {
            "North Beach": 22,
            "Fisherman's Wharf": 25,
            "Haight-Ashbury": 19,
            "Nob Hill": 20,
            "Golden Gate Park": 22,
            "Union Square": 18,
            "Alamo Square": 16,
            "Presidio": 32,
            "Chinatown": 19,
            "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25,
            "Fisherman's Wharf": 5,
            "Haight-Ashbury": 18,
            "Nob Hill": 7,
            "Golden Gate Park": 22,
            "Union Square": 7,
            "Alamo Square": 16,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "North Beach": 6,
            "Haight-Ashbury": 22,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Union Square": 13,
            "Alamo Square": 21,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Union Square": 19,
            "Alamo Square": 5,
            "Presidio": 15,
            "Chinatown": 19,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13,
            "Golden Gate Park": 17,
            "Union Square": 7,
            "Alamo Square": 11,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23,
            "North Beach": 23,
            "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7,
            "Nob Hill": 20,
            "Union Square": 22,
            "Alamo Square": 9,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18,
            "Nob Hill": 9,
            "Golden Gate Park": 22,
            "Alamo Square": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Union Square": 14,
            "Presidio": 17,
            "Chinatown": 15,
            "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15,
            "Nob Hill": 18,
            "Golden Gate Park": 12,
            "Union Square": 22,
            "Alamo Square": 19,
            "Chinatown": 21,
            "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20,
            "North Beach": 3,
            "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19,
            "Nob Hill": 9,
            "Golden Gate Park": 23,
            "Union Square": 7,
            "Alamo Square": 17,
            "Presidio": 19,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22,
            "North Beach": 9,
            "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Union Square": 12,
            "Alamo Square": 10,
            "Presidio": 11,
            "Chinatown": 11
        }
    }

    meetings = [
        {"name": "Brian", "location": "North Beach", "available_start": 780, "available_end": 1140, "min_duration": 90},
        {"name": "Richard", "location": "Fisherman's Wharf", "available_start": 660, "available_end": 765, "min_duration": 60},
        {"name": "Ashley", "location": "Haight-Ashbury", "available_start": 900, "available_end": 1230, "min_duration": 90},
        {"name": "Elizabeth", "location": "Nob Hill", "available_start": 705, "available_end": 1110, "min_duration": 75},
        {"name": "Jessica", "location": "Golden Gate Park", "available_start": 1200, "available_end": 1245, "min_duration": 105},
        {"name": "Deborah", "location": "Union Square", "available_start": 1050, "available_end": 1320, "min_duration": 60},
        {"name": "Kimberly", "location": "Alamo Square", "available_start": 1050, "available_end": 1275, "min_duration": 45},
        {"name": "Matthew", "location": "Presidio", "available_start": 495, "available_end": 540, "min_duration": 15},
        {"name": "Kenneth", "location": "Chinatown", "available_start": 825, "available_end": 1170, "min_duration": 105},
        {"name": "Anthony", "location": "Pacific Heights", "available_start": 855, "available_end": 960, "min_duration": 30}
    ]

    heap = []
    heapq.heappush(heap, (-0, 540, "Bayview", 0, []))
    best = {}

    while heap:
        neg_num_meetings, current_time, current_location, mask, path = heapq.heappop(heap)
        num_meetings = -neg_num_meetings

        key = (current_location, mask)
        if key in best and best[key][0] >= num_meetings:
            continue
        best[key] = (num_meetings, current_time, path)

        for i in range(len(meetings)):
            if not (mask & (1 << i)):
                meeting = meetings[i]
                loc = meeting["location"]
                travel_time = travel_times[current_location][loc]
                arrival_time = current_time + travel_time

                available_start = meeting["available_start"]
                available_end = meeting["available_end"]
                min_duration = meeting["min_duration"]

                start_time = max(arrival_time, available_start)
                end_time = start_time + min_duration

                if end_time > available_end:
                    continue

                new_time = end_time
                new_mask = mask | (1 << i)
                new_path = path + [i]
                new_num_meetings = num_meetings + 1

                heapq.heappush(heap, (-new_num_meetings, new_time, loc, new_mask, new_path))

    max_meetings = 0
    best_path = []
    for key in best:
        num_meetings, time, path = best[key]
        if num_meetings > max_meetings:
            max_meetings = num_meetings
            best_path = path

    itinerary = []
    current_time = 540
    current_location = "Bayview"
    for i in best_path:
        meeting = meetings[i]
        loc = meeting["location"]
        travel_time = travel_times[current_location][loc]
        arrival_time = current_time + travel_time

        available_start = meeting["available_start"]
        available_end = meeting["available_end"]
        min_duration = meeting["min_duration"]

        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": meeting["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })

        current_time = end_time
        current_location = loc

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()