import json

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def add_time(t, delta_minutes):
    """Add minutes to a time string, return time string."""
    m = time_to_minutes(t) + delta_minutes
    return minutes_to_time(m)

def main():
    # Travel times matrix: from_index to to_index in minutes
    locations = ["Presidio", "Golden Gate Park", "Bayview", "Chinatown", "North Beach", "Mission District"]
    loc_index = {loc: i for i, loc in enumerate(locations)}
    
    travel = [
        [0, 12, 31, 21, 18, 26],  # Presidio
        [11, 0, 23, 23, 24, 17],  # Golden Gate Park
        [31, 22, 0, 18, 21, 13],  # Bayview
        [19, 23, 22, 0, 3, 18],   # Chinatown
        [17, 22, 22, 6, 0, 18],   # North Beach
        [25, 17, 15, 16, 17, 0]   # Mission District
    ]
    
    # People data: name, location, window start, window end, min_duration (min)
    people = [
        ("Jessica", "Golden Gate Park", "13:45", "15:00", 30),
        ("Ashley", "Bayview", "17:15", "20:00", 105),
        ("Ronald", "Chinatown", "7:15", "14:45", 90),
        ("William", "North Beach", "13:15", "20:15", 15),
        ("Daniel", "Mission District", "7:00", "11:15", 105)
    ]
    
    # We'll compute the schedule we derived
    itinerary = []
    current_time = "9:00"
    current_loc = "Presidio"
    
    # 1. Go to Daniel at Mission District
    travel_time = travel[loc_index[current_loc]][loc_index["Mission District"]]
    arrival = add_time(current_time, travel_time)
    start_meeting = max(arrival, "7:00")  # Daniel available 7:00
    # We can start at arrival (9:26) since it's after 7:00
    end_meeting = add_time(start_meeting, 105)  # meet exactly 105 min
    if time_to_minutes(end_meeting) > time_to_minutes("11:15"):
        end_meeting = "11:15"  # but Daniel leaves at 11:15, so adjust if needed
    # Actually we want to maximize time but ensure min 105: from 9:26 to 11:15 is 109 min, so ok.
    # Let's just end at 11:15 to maximize time with him.
    end_meeting = "11:15"
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Daniel",
        "start_time": start_meeting,
        "end_time": end_meeting
    })
    
    current_time = end_meeting
    current_loc = "Mission District"
    
    # 2. Go to Ronald at Chinatown
    travel_time = travel[loc_index[current_loc]][loc_index["Chinatown"]]
    arrival = add_time(current_time, travel_time)
    start_meeting = max(arrival, "7:15")
    end_meeting = add_time(start_meeting, 90)
    if time_to_minutes(end_meeting) > time_to_minutes("14:45"):
        end_meeting = "14:45"
    itinerary.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Ronald",
        "start_time": start_meeting,
        "end_time": end_meeting
    })
    
    current_time = end_meeting
    current_loc = "Chinatown"
    
    # 3. Go to Jessica at Golden Gate Park
    travel_time = travel[loc_index[current_loc]][loc_index["Golden Gate Park"]]
    arrival = add_time(current_time, travel_time)
    # Jessica starts at 13:45
    start_meeting = max(arrival, "13:45")
    end_meeting = add_time(start_meeting, 30)
    if time_to_minutes(end_meeting) > time_to_minutes("15:00"):
        end_meeting = "15:00"
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Jessica",
        "start_time": start_meeting,
        "end_time": end_meeting
    })
    
    current_time = end_meeting
    current_loc = "Golden Gate Park"
    
    # 4. Go to William at North Beach
    travel_time = travel[loc_index[current_loc]][loc_index["North Beach"]]
    arrival = add_time(current_time, travel_time)
    start_meeting = max(arrival, "13:15")
    end_meeting = add_time(start_meeting, 15)
    itinerary.append({
        "action": "meet",
        "location": "North Beach",
        "person": "William",
        "start_time": start_meeting,
        "end_time": end_meeting
    })
    
    current_time = end_meeting
    current_loc = "North Beach"
    
    # 5. Go to Ashley at Bayview
    travel_time = travel[loc_index[current_loc]][loc_index["Bayview"]]
    arrival = add_time(current_time, travel_time)
    start_meeting = max(arrival, "17:15")
    end_meeting = add_time(start_meeting, 105)
    if time_to_minutes(end_meeting) > time_to_minutes("20:00"):
        end_meeting = "20:00"
    itinerary.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Ashley",
        "start_time": start_meeting,
        "end_time": end_meeting
    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()