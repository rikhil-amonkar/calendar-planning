import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times in minutes between locations
    travel_times = {
        "Nob Hill": {"Richmond District":14, "Financial District":9, "North Beach":8, "The Castro":17, "Golden Gate Park":17},
        "Richmond District": {"Nob Hill":17, "Financial District":22, "North Beach":17, "The Castro":16, "Golden Gate Park":9},
        "Financial District": {"Nob Hill":8, "Richmond District":21, "North Beach":7, "The Castro":23, "Golden Gate Park":23},
        "North Beach": {"Nob Hill":7, "Richmond District":18, "Financial District":8, "The Castro":22, "Golden Gate Park":22},
        "The Castro": {"Nob Hill":16, "Richmond District":16, "Financial District":20, "North Beach":20, "Golden Gate Park":11},
        "Golden Gate Park": {"Nob Hill":20, "Richmond District":7, "Financial District":26, "North Beach":24, "The Castro":13}
    }
    
    # Meeting constraints as input variables.
    # Times are expressed in minutes since midnight.
    meetings = [
        {
            "person": "Jeffrey",
            "location": "Golden Gate Park",
            "avail_start": 11 * 60 + 15,  # 11:15
            "avail_end": 14 * 60 + 30,    # 14:30
            "duration": 120             # minutes
        },
        {
            "person": "Deborah",
            "location": "The Castro",
            "avail_start": 13 * 60 + 45,  # 13:45
            "avail_end": 21 * 60 + 15,    # 21:15
            "duration": 90
        },
        {
            "person": "Margaret",
            "location": "Financial District",
            "avail_start": 16 * 60 + 30,  # 16:30
            "avail_end": 20 * 60 + 15,    # 20:15
            "duration": 75
        },
        {
            "person": "Ronald",
            "location": "North Beach",
            "avail_start": 18 * 60 + 30,  # 18:30
            "avail_end": 19 * 60 + 30,    # 19:30
            "duration": 45
        },
        {
            "person": "Emily",
            "location": "Richmond District",
            "avail_start": 19 * 60,       # 19:00
            "avail_end": 21 * 60,         # 21:00
            "duration": 15
        }
    ]
    
    # Starting parameters
    current_location = "Nob Hill"
    current_time = 9 * 60    # 9:00 in minutes

    itinerary = []

    # Define order based on computed optimal route: Jeffrey, Deborah, Margaret, Ronald, Emily.
    for meeting in meetings:
        target_location = meeting["location"]
        # Get travel time from current location to target location
        if current_location == target_location:
            travel = 0
        else:
            travel = travel_times[current_location][target_location]
            
        # Update time with travel
        current_time += travel
        
        # Wait if arriving earlier than available start time
        meeting_start = max(current_time, meeting["avail_start"])
        
        # Schedule meeting for the required duration
        meeting_end = meeting_start + meeting["duration"]
        
        # Update itinerary with this meeting details
        itinerary.append({
            "action": "meet",
            "location": target_location,
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location after meeting
        current_time = meeting_end
        current_location = target_location

    # Build resulting JSON dictionary
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()