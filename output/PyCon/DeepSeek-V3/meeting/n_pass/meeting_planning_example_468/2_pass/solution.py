import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, "%H:%M")
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        "The Castro": {
            "Bayview": 19, "Pacific Heights": 16, "Alamo Square": 8,
            "Fisherman's Wharf": 24, "Golden Gate Park": 11
        },
        "Bayview": {
            "The Castro": 20, "Pacific Heights": 23, "Alamo Square": 16,
            "Fisherman's Wharf": 25, "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "The Castro": 16, "Bayview": 22, "Alamo Square": 10,
            "Fisherman's Wharf": 13, "Golden Gate Park": 15
        },
        "Alamo Square": {
            "The Castro": 8, "Bayview": 16, "Pacific Heights": 10,
            "Fisherman's Wharf": 19, "Golden Gate Park": 9
        },
        "Fisherman's Wharf": {
            "The Castro": 26, "Bayview": 26, "Pacific Heights": 12,
            "Alamo Square": 20, "Golden Gate Park": 25
        },
        "Golden Gate Park": {
            "The Castro": 13, "Bayview": 23, "Pacific Heights": 16,
            "Alamo Square": 10, "Fisherman's Wharf": 24
        }
    }
    
    # Person constraints
    people = {
        "Rebecca": {
            "location": "Bayview",
            "available_start": "9:00",
            "available_end": "12:45",
            "min_duration": 90
        },
        "Amanda": {
            "location": "Pacific Heights", 
            "available_start": "18:30",
            "available_end": "21:45",
            "min_duration": 90
        },
        "James": {
            "location": "Alamo Square",
            "available_start": "9:45", 
            "available_end": "21:15",
            "min_duration": 90
        },
        "Sarah": {
            "location": "Fisherman's Wharf",
            "available_start": "8:00",
            "available_end": "21:30", 
            "min_duration": 90
        },
        "Melissa": {
            "location": "Golden Gate Park",
            "available_start": "9:00",
            "available_end": "18:45",
            "min_duration": 90
        }
    }
    
    # Convert all times to minutes
    start_time = time_to_minutes("9:00")  # Start at The Castro
    
    # Create a list of people with their constraints
    person_list = []
    for name, info in people.items():
        person_list.append({
            "name": name,
            "location": info["location"],
            "available_start": time_to_minutes(info["available_start"]),
            "available_end": time_to_minutes(info["available_end"]),
            "min_duration": info["min_duration"]
        })
    
    # Try to schedule meetings greedily
    current_time = start_time
    current_location = "The Castro"
    scheduled_meetings = []
    
    # Keep trying until no more meetings can be scheduled
    remaining_people = person_list.copy()
    scheduled_any = True
    
    while scheduled_any and remaining_people:
        scheduled_any = False
        best_next_meeting = None
        best_end_time = float('inf')
        
        # Find the best next meeting (earliest possible end time)
        for person in remaining_people:
            # Calculate earliest possible start time for this meeting
            travel_time = travel_times[current_location][person["location"]]
            earliest_start = current_time + travel_time
            
            # Check if this fits within person's availability
            actual_start = max(earliest_start, person["available_start"])
            end_time = actual_start + person["min_duration"]
            
            # Check if meeting can be completed within person's availability
            if (actual_start >= person["available_start"] and 
                end_time <= person["available_end"] and
                end_time < best_end_time):
                
                best_next_meeting = person
                best_end_time = end_time
                best_start = actual_start
        
        if best_next_meeting:
            # Schedule this meeting
            scheduled_meetings.append({
                "person": best_next_meeting["name"],
                "location": best_next_meeting["location"],
                "start": best_start,
                "end": best_end_time
            })
            
            # Update current state
            current_time = best_end_time
            current_location = best_next_meeting["location"]
            
            # Remove from remaining people
            remaining_people.remove(best_next_meeting)
            scheduled_any = True
    
    # Build itinerary
    itinerary = []
    current_location = "The Castro"
    current_time = start_time
    
    for i, meeting in enumerate(scheduled_meetings):
        # Add travel to meeting location
        travel_time = travel_times[current_location][meeting["location"]]
        travel_end = current_time + travel_time
        
        itinerary.append({
            "action": "travel",
            "from": current_location,
            "to": meeting["location"],
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(travel_end)
        })
        
        # Add the meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
        
        # Update current state
        current_location = meeting["location"]
        current_time = meeting["end"]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()