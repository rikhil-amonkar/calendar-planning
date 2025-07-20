import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times dictionary
    travel_times = {
        "Richmond District": {
            "Marina District": 9,
            "Chinatown": 20,
            "Financial District": 22,
            "Bayview": 26,
            "Union Square": 21
        },
        "Marina District": {
            "Richmond District": 11,
            "Chinatown": 16,
            "Financial District": 17,
            "Bayview": 27,
            "Union Square": 16
        },
        "Chinatown": {
            "Richmond District": 20,
            "Marina District": 12,
            "Financial District": 5,
            "Bayview": 22,
            "Union Square": 7
        },
        "Financial District": {
            "Richmond District": 21,
            "Marina District": 15,
            "Chinatown": 5,
            "Bayview": 19,
            "Union Square": 9
        },
        "Bayview": {
            "Richmond District": 25,
            "Marina District": 25,
            "Chinatown": 18,
            "Financial District": 19,
            "Union Square": 17
        },
        "Union Square": {
            "Richmond District": 20,
            "Marina District": 18,
            "Chinatown": 7,
            "Financial District": 9,
            "Bayview": 15
        }
    }
    
    # Convert time constraints to minutes
    start_time = 9 * 60  # 9:00 AM
    
    # Friend constraints: (name, location, available_start, available_end, duration)
    friends = [
        ("Margaret", "Bayview", 9*60+30, 13*60+30, 30),
        ("Robert", "Chinatown", 12*60+15, 20*60+15, 15),
        ("Kimberly", "Marina District", 13*60+15, 16*60+45, 15),
        ("Rebecca", "Financial District", 13*60+15, 16*60+45, 75),
        ("Kenneth", "Union Square", 19*60+30, 21*60+15, 75)
    ]
    
    # Fixed meeting order: Margaret -> Robert -> Kimberly -> Rebecca -> Kenneth
    meeting_order = [
        (friends[0][0], friends[0][1], friends[0][2], friends[0][3], friends[0][4]),  # Margaret
        (friends[1][0], friends[1][1], friends[1][2], friends[1][3], friends[1][4]),  # Robert
        (friends[2][0], friends[2][1], friends[2][2], friends[2][3], friends[2][4]),  # Kimberly
        (friends[3][0], friends[3][1], friends[3][2], friends[3][3], friends[3][4]),  # Rebecca
        (friends[4][0], friends[4][1], friends[4][2], friends[4][3], friends[4][4])   # Kenneth
    ]
    
    # Initialize
    current_location = "Richmond District"
    current_time = start_time
    itinerary = []
    
    # Process each meeting in order
    for name, location, avail_start, avail_end, duration in meeting_order:
        # Travel to the meeting location
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Start meeting at the later of arrival time or friend's available time
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + duration
        
        # Check if meeting can be completed within friend's availability
        if meeting_end > avail_end:
            # If not feasible, adjust to end at available end time
            meeting_start = avail_end - duration
            meeting_end = avail_end
        
        # Add meeting to itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": format_time(meeting_start),
            "end_time": format_time(meeting_end)
        })
        
        # Update current location and time for next meeting
        current_location = location
        current_time = meeting_end
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()