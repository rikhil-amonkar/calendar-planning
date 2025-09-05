import itertools
import json

def time_to_minutes(time_str):
    # Convert time string "H:MM" to minutes since midnight
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    # Convert minutes since midnight to time string "H:MM" (24-hour format)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7,
    }
    
    # Starting point and arrival time at North Beach
    start_location = "North Beach"
    start_time = time_to_minutes("9:00")
    
    # Meeting constraints for each friend
    meetings = [
        {
            "person": "James",
            "location": "Mission District",
            "available_start": "12:45",
            "available_end": "14:00",
            "min_duration": 75
        },
        {
            "person": "Robert",
            "location": "The Castro",
            "available_start": "12:45",
            "available_end": "15:15",
            "min_duration": 30
        }
    ]
    
    best_schedule = None
    best_count = 0
    
    # Try all possible orders in which to meet friends
    for order in itertools.permutations(meetings):
        current_time = start_time
        current_location = start_location
        schedule = []
        feasible = True
        
        for meeting in order:
            # Calculate travel time from current location to meeting location
            key = (current_location, meeting["location"])
            if key not in travel_times:
                feasible = False
                break
            travel_time = travel_times[key]
            arrival_time = current_time + travel_time
            
            # Friend is only available starting at this time
            friend_available_start = time_to_minutes(meeting["available_start"])
            friend_available_end = time_to_minutes(meeting["available_end"])
            
            # Meeting can only start when the friend is available
            meeting_start = max(arrival_time, friend_available_start)
            meeting_end = meeting_start + meeting["min_duration"]
            
            # Check if the meeting can be concluded before the friend leaves
            if meeting_end > friend_available_end:
                feasible = False
                break
            
            # Add meeting event to the itinerary
            event = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
            schedule.append(event)
            
            # Update current time and location after the meeting
            current_time = meeting_end
            current_location = meeting["location"]
        
        # Keep the schedule that covers more meetings (goal: meet as many friends as possible)
        if feasible and len(schedule) > best_count:
            best_schedule = schedule
            best_count = len(schedule)
    
    # Output the final itinerary as a JSON-formatted dictionary
    result = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(result))

if __name__ == '__main__':
    main()