import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7,
}

# Meeting times and constraints
arrival_time = datetime.strptime("9:00", "%H:%M")
james_start = datetime.strptime("12:45", "%H:%M")
james_end = datetime.strptime("14:00", "%H:%M")
james_meeting_duration = timedelta(minutes=75)

robert_start = datetime.strptime("12:45", "%H:%M")
robert_end = datetime.strptime("15:15", "%H:%M")
robert_meeting_duration = timedelta(minutes=30)

def optimal_schedule():
    itinerary = []
    
    # Time when we can start meeting since we will arrive at North Beach at 9:00
    current_time = arrival_time
    
    # Meet James first
    # Need to leave North Beach by 12:27 (12:45 - 18 minutes travel time)
    time_to_meet_james = james_start - timedelta(minutes=travel_times[("North Beach", "Mission District")])
    
    if current_time < time_to_meet_james:
        # Schedule to meet James from 12:27 to 13:42
        james_meeting_start = time_to_meet_james
        james_meeting_end = james_meeting_start + james_meeting_duration
        
        if james_meeting_end <= james_end:
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": james_meeting_start.strftime("%H:%M"),
                "end_time": james_meeting_end.strftime("%H:%M"),
            })
            current_time = james_meeting_end + timedelta(minutes=travel_times[("Mission District", "The Castro")])
    
    # Now we will meet Robert at The Castro
    # We must arrive by 15:15 - 22 minutes (travel from The Castro to North Beach)
    time_to_meet_robert = robert_end - timedelta(minutes=travel_times[("The Castro", "North Beach")])
    
    if current_time < robert_start:
        # Wait until Robert is available at 12:45
        current_time = robert_start
        
    # Schedule to meet Robert for the minimum duration possible
    robert_meeting_start = current_time
    robert_meeting_end = robert_meeting_start + robert_meeting_duration
    
    if robert_meeting_end <= robert_end:
        itinerary.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": robert_meeting_start.strftime("%H:%M"),
            "end_time": robert_meeting_end.strftime("%H:%M"),
        })
    
    result = {
        "itinerary": itinerary
    }
    
    return json.dumps(result, indent=4)

# Run the program
if __name__ == "__main__":
    print(optimal_schedule())