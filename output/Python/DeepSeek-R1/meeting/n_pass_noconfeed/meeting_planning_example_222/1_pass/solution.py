import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        "Nob Hill": {
            "North Beach": 8,
            "Fisherman's Wharf": 11,
            "Bayview": 19
        },
        "North Beach": {
            "Nob Hill": 7,
            "Fisherman's Wharf": 5,
            "Bayview": 22
        },
        "Fisherman's Wharf": {
            "Nob Hill": 11,
            "North Beach": 6,
            "Bayview": 26
        },
        "Bayview": {
            "Nob Hill": 20,
            "North Beach": 21,
            "Fisherman's Wharf": 25
        }
    }
    
    friends = [
        {
            "name": "Helen",
            "location": "North Beach",
            "available_start": 7 * 60,       # 7:00 in minutes
            "available_end": 16 * 60 + 45,   # 16:45 in minutes
            "min_duration": 120
        },
        {
            "name": "Kimberly",
            "location": "Fisherman's Wharf",
            "available_start": 16 * 60 + 30, # 16:30 in minutes
            "available_end": 21 * 60,        # 21:00 in minutes
            "min_duration": 45
        },
        {
            "name": "Patricia",
            "location": "Bayview",
            "available_start": 18 * 60,      # 18:00 in minutes
            "available_end": 21 * 60 + 15,   # 21:15 in minutes
            "min_duration": 120
        }
    ]
    
    itinerary = []
    current_time = 9 * 60   # 9:00 in minutes
    
    # Travel to Helen at North Beach
    travel_time0 = travel_times["Nob Hill"][friends[0]["location"]]
    current_time += travel_time0   # arrival time at Helen's location
    
    # Calculate the end time for Helen
    travel_time0_to_1 = travel_times[friends[0]["location"]][friends[1]["location"]]
    travel_time1_to_2 = travel_times[friends[1]["location"]][friends[2]["location"]]
    total_time = travel_time0_to_1 + friends[1]["min_duration"] + travel_time1_to_2 + friends[2]["min_duration"]
    latest_end0 = friends[2]["available_end"] - total_time
    candidate1 = friends[0]["available_end"]
    candidate2 = friends[1]["available_end"] - friends[1]["min_duration"] - travel_time0_to_1
    end0 = min(candidate1, candidate2, latest_end0)
    start0 = current_time
    
    itinerary.append({
        "action": "meet",
        "location": friends[0]["location"],
        "person": friends[0]["name"],
        "start_time": minutes_to_time(start0),
        "end_time": minutes_to_time(end0)
    })
    
    # Travel to Kimberly at Fisherman's Wharf
    current_time = end0 + travel_time0_to_1
    start1 = current_time
    end1 = start1 + friends[1]["min_duration"]
    
    itinerary.append({
        "action": "meet",
        "location": friends[1]["location"],
        "person": friends[1]["name"],
        "start_time": minutes_to_time(start1),
        "end_time": minutes_to_time(end1)
    })
    
    # Travel to Patricia at Bayview
    current_time = end1 + travel_time1_to_2
    start2 = max(current_time, friends[2]["available_start"])
    end2 = start2 + friends[2]["min_duration"]
    
    itinerary.append({
        "action": "meet",
        "location": friends[2]["location"],
        "person": friends[2]["name"],
        "start_time": minutes_to_time(start2),
        "end_time": minutes_to_time(end2)
    })
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()