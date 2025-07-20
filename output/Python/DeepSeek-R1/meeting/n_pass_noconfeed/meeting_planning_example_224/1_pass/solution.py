import json

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Presidio"): 7
    }
    
    start_time_minutes = 9 * 60  # 9:00 AM in minutes from midnight
    
    itinerary = []
    
    # Meet Melissa at Golden Gate Park
    travel_duration_fw_to_ggp = travel_times[("Fisherman's Wharf", "Golden Gate Park")]
    arrival_melissa = start_time_minutes + travel_duration_fw_to_ggp
    meet_melissa_start = arrival_melissa
    meet_melissa_end = meet_melissa_start + 15
    itinerary.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Melissa",
        "start_time": min_to_time(meet_melissa_start),
        "end_time": min_to_time(meet_melissa_end)
    })
    
    # Meet Emily at Richmond District (must arrive by 16:45)
    travel_duration_ggp_to_rd = travel_times[("Golden Gate Park", "Richmond District")]
    emily_available_start = 16 * 60 + 45
    meet_emily_start = emily_available_start
    meet_emily_end = meet_emily_start + 120
    itinerary.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Emily",
        "start_time": min_to_time(meet_emily_start),
        "end_time": min_to_time(meet_emily_end)
    })
    
    # Meet Nancy at Presidio (must start at 19:45)
    travel_duration_rd_to_p = travel_times[("Richmond District", "Presidio")]
    nancy_available_start = 19 * 60 + 45
    meet_nancy_start = nancy_available_start
    meet_nancy_end = meet_nancy_start + 105
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Nancy",
        "start_time": min_to_time(meet_nancy_start),
        "end_time": min_to_time(meet_nancy_end)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()