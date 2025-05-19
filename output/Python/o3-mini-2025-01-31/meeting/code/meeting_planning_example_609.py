import json
from datetime import timedelta, datetime

def time_to_minutes(t):
    # t in format "H:MM", 24-hour format, no leading zero required.
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    # returns time string in H:MM format, no leading zero for hours.
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define travel times dictionary (in minutes)
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Meeting constraints for each friend:
# Each entry: person, location, availability start, availability end, meeting duration (in minutes)
meetings = [
    {"person": "David", "location": "Mission District", "avail_start": "8:00", "avail_end": "19:45", "duration": 45},
    {"person": "Deborah", "location": "Golden Gate Park", "avail_start": "7:00", "avail_end": "18:15", "duration": 90},
    {"person": "Kenneth", "location": "Alamo Square", "avail_start": "14:00", "avail_end": "19:45", "duration": 120},
    {"person": "John", "location": "Pacific Heights", "avail_start": "17:00", "avail_end": "20:00", "duration": 15},
    {"person": "Karen", "location": "Sunset District", "avail_start": "17:45", "avail_end": "21:15", "duration": 15},
    {"person": "Charles", "location": "Union Square", "avail_start": "21:45", "avail_end": "22:45", "duration": 60},
    {"person": "Carol", "location": "Presidio", "avail_start": "8:15", "avail_end": "9:15", "duration": 30},
]

# To maximize the number of friends met, we will try an order that allows as many meetings as possible.
# After analysis, Carol's availability window is too early (before we can reach her from Chinatown),
# so we exclude Carol if not feasible.
# We'll order the meetings by their availability start time (except Carol which will likely be skipped).
def compute_schedule():
    # Starting point: Arrive at Chinatown at 9:00
    current_location = "Chinatown"
    current_time = time_to_minutes("9:00")
    
    itinerary = []
    
    # Define the order manually based on optimization analysis:
    # We'll attempt to schedule: David, Deborah, Kenneth, John, Karen, Charles, then try Carol at the end.
    order = ["David", "Deborah", "Kenneth", "John", "Karen", "Charles", "Carol"]
    meetings_ordered = []
    for name in order:
        for mt in meetings:
            if mt["person"] == name:
                meetings_ordered.append(mt)
                break

    for meeting in meetings_ordered:
        # Check travel time from current location to meeting location
        key = (current_location, meeting["location"])
        if key in travel_times:
            travel_time = travel_times[key]
        else:
            # If not defined, assume symmetric travel (should be defined actually)
            key = (meeting["location"], current_location)
            travel_time = travel_times.get(key, 0)
        # Compute arrival time at meeting location
        arrival_time = current_time + travel_time
        
        # Convert meeting availability times to minutes
        avail_start = time_to_minutes(meeting["avail_start"])
        avail_end   = time_to_minutes(meeting["avail_end"])
        
        # The meeting can start only after arrival and avail_start
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + meeting["duration"]
        
        # Check if meeting end is within availability window
        if meeting_end > avail_end:
            # Cannot schedule this meeting; skip it.
            # Debug: print("Skipping meeting with", meeting["person"])
            continue
        
        # Append meeting to itinerary with formatted times
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        # Update current time and location for next travel
        current_time = meeting_end
        current_location = meeting["location"]
    
    return {"itinerary": itinerary}

def main():
    schedule = compute_schedule()
    # Output the result as JSON formatted string.
    print(json.dumps(schedule, indent=2))

if __name__ == '__main__':
    main()