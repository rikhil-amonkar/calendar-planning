import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        "Sunset District": {"Alamo Square": 17, "Russian Hill": 24, "Golden Gate Park": 11, "Mission District": 24},
        "Alamo Square": {"Sunset District": 16, "Russian Hill": 13, "Golden Gate Park": 9, "Mission District": 10},
        "Russian Hill": {"Sunset District": 23, "Alamo Square": 15, "Golden Gate Park": 21, "Mission District": 16},
        "Golden Gate Park": {"Sunset District": 10, "Alamo Square": 10, "Russian Hill": 19, "Mission District": 17},
        "Mission District": {"Sunset District": 24, "Alamo Square": 11, "Russian Hill": 15, "Golden Gate Park": 17}
    }
    
    current_location = "Sunset District"
    current_time = 540  # 9:00 AM in minutes (540 minutes from midnight)
    
    itinerary = []
    
    # Meeting Daniel at Golden Gate Park
    travel = travel_times[current_location]["Golden Gate Park"]
    arrival = current_time + travel
    meet_start = arrival
    meet_end = meet_start + 15
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Daniel",
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    current_location = "Golden Gate Park"
    current_time = meet_end
    
    # Meeting Margaret at Russian Hill
    travel = travel_times[current_location]["Russian Hill"]
    arrival = current_time + travel
    meet_start = arrival
    meet_end = meet_start + 30
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "Margaret",
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    current_location = "Russian Hill"
    current_time = meet_end
    
    # Travel to Alamo Square for Charles
    travel = travel_times[current_location]["Alamo Square"]
    departure = 1080 - travel  # arrive at 18:00 (1080 minutes)
    meet_start = 1080
    meet_end = meet_start + 90
    itinerary.append({
        "action": "meet",
        "location": "Alamo Square",
        "person": "Charles",
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    current_location = "Alamo Square"
    current_time = meet_end
    
    # Meeting Stephanie at Mission District
    travel = travel_times[current_location]["Mission District"]
    arrival = current_time + travel
    meet_start = 1230  # Stephanie's availability starts at 20:30 (1230 minutes)
    meet_end = meet_start + 90
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Stephanie",
        "start_time": minutes_to_time(meet_start),
        "end_time": minutes_to_time(meet_end)
    })
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()