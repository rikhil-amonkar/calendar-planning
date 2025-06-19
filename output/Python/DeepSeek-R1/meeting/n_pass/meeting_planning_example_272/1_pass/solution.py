import json

def main():
    travel_times = {
        'Russian Hill': {'Nob Hill': 5, 'Mission District': 16, 'Embarcadero': 8},
        'Nob Hill': {'Russian Hill': 5, 'Mission District': 13, 'Embarcadero': 9},
        'Mission District': {'Russian Hill': 15, 'Nob Hill': 12, 'Embarcadero': 19},
        'Embarcadero': {'Russian Hill': 8, 'Nob Hill': 10, 'Mission District': 20}
    }
    
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{int(hours)}:{mins:02d}"
    
    current_time = 540  # 9:00 AM in minutes
    current_loc = "Russian Hill"
    itinerary = []
    
    # Schedule Timothy at Embarcadero
    next_loc = "Embarcadero"
    travel_time_val = travel_times[current_loc][next_loc]
    depart_time = 585 - travel_time_val  # 585 is 9:45 AM
    start_meeting = 585
    end_meeting = 585 + 120  # 11:45 AM
    itinerary.append({
        "action": "meet",
        "location": next_loc,
        "person": "Timothy",
        "start_time": format_time(start_meeting),
        "end_time": format_time(end_meeting)
    })
    current_time = end_meeting
    current_loc = next_loc
    
    # Schedule Patricia at Nob Hill
    next_loc = "Nob Hill"
    travel_time_val = travel_times[current_loc][next_loc]
    depart_time = 1110 - travel_time_val  # 1110 is 6:30 PM
    start_meeting = 1110
    end_meeting = 1110 + 90  # 8:00 PM
    itinerary.append({
        "action": "meet",
        "location": next_loc,
        "person": "Patricia",
        "start_time": format_time(start_meeting),
        "end_time": format_time(end_meeting)
    })
    current_time = end_meeting
    current_loc = next_loc
    
    # Schedule Ashley at Mission District
    next_loc = "Mission District"
    start_meeting = 1230  # 8:30 PM
    end_meeting = 1230 + 45  # 9:15 PM
    itinerary.append({
        "action": "meet",
        "location": next_loc,
        "person": "Ashley",
        "start_time": format_time(start_meeting),
        "end_time": format_time(end_meeting)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()