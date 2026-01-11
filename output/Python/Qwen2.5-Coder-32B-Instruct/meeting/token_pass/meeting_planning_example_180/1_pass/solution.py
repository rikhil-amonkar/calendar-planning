import json
from datetime import datetime, timedelta

# Define the start time
start_time = datetime.strptime("9:00", "%H:%M")

# Define the travel times in minutes
travel_times = {
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7
}

# Define the meeting constraints
meeting_constraints = {
    "James": {"location": "Mission District", "start": "12:45", "end": "14:00", "min_duration": 75},
    "Robert": {"location": "The Castro", "start": "12:45", "end": "15:15", "min_duration": 30}
}

def calculate_meeting_time(start, end, min_duration):
    start_time = datetime.strptime(start, "%H:%M")
    end_time = datetime.strptime(end, "%H:%M")
    duration = timedelta(minutes=min_duration)
    
    if end_time - start_time >= duration:
        return start_time, start_time + duration
    else:
        return None, None

def convert_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_from_minutes(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes}"

def find_optimal_schedule(start_time, travel_times, meeting_constraints):
    itinerary = []
    
    # Calculate possible meeting times
    james_start, james_end = calculate_meeting_time(meeting_constraints["James"]["start"], meeting_constraints["James"]["end"], meeting_constraints["James"]["min_duration"])
    robert_start, robert_end = calculate_meeting_time(meeting_constraints["Robert"]["start"], meeting_constraints["Robert"]["end"], meeting_constraints["Robert"]["min_duration"])
    
    # Check if we can meet James first
    if james_start and james_end:
        # Check if we can travel to Mission District in time
        travel_to_james = travel_times[("North Beach", meeting_constraints["James"]["location"])]
        if start_time + timedelta(minutes=travel_to_james) <= james_start:
            # Add James meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": meeting_constraints["James"]["location"],
                "person": "James",
                "start_time": james_start.strftime("%H:%M"),
                "end_time": james_end.strftime("%H:%M")
            })
            # Update current time after meeting James
            current_time = james_end + timedelta(minutes=travel_times[(meeting_constraints["James"]["location"], "North Beach")])
            
            # Check if we can meet Robert after meeting James
            if current_time + timedelta(minutes=travel_times[("North Beach", meeting_constraints["Robert"]["location"])]) <= robert_start:
                travel_to_robert = travel_times[("North Beach", meeting_constraints["Robert"]["location"])]
                current_time += timedelta(minutes=travel_to_robert)
                if current_time + timedelta(minutes=meeting_constraints["Robert"]["min_duration"]) <= robert_end:
                    # Add Robert meeting to itinerary
                    itinerary.append({
                        "action": "meet",
                        "location": meeting_constraints["Robert"]["location"],
                        "person": "Robert",
                        "start_time": current_time.strftime("%H:%M"),
                        "end_time": (current_time + timedelta(minutes=meeting_constraints["Robert"]["min_duration"])).strftime("%H:%M")
                    })
        else:
            # Check if we can meet Robert first
            if robert_start and robert_end:
                travel_to_robert = travel_times[("North Beach", meeting_constraints["Robert"]["location"])]
                if start_time + timedelta(minutes=travel_to_robert) <= robert_start:
                    # Add Robert meeting to itinerary
                    itinerary.append({
                        "action": "meet",
                        "location": meeting_constraints["Robert"]["location"],
                        "person": "Robert",
                        "start_time": robert_start.strftime("%H:%M"),
                        "end_time": robert_end.strftime("%H:%M")
                    })
                    # Update current time after meeting Robert
                    current_time = robert_end + timedelta(minutes=travel_times[(meeting_constraints["Robert"]["location"], "North Beach")])
                    
                    # Check if we can meet James after meeting Robert
                    if current_time + timedelta(minutes=travel_times[("North Beach", meeting_constraints["James"]["location"])]) <= james_start:
                        travel_to_james = travel_times[("North Beach", meeting_constraints["James"]["location"])]
                        current_time += timedelta(minutes=travel_to_james)
                        if current_time + timedelta(minutes=meeting_constraints["James"]["min_duration"]) <= james_end:
                            # Add James meeting to itinerary
                            itinerary.append({
                                "action": "meet",
                                "location": meeting_constraints["James"]["location"],
                                "person": "James",
                                "start_time": current_time.strftime("%H:%M"),
                                "end_time": (current_time + timedelta(minutes=meeting_constraints["James"]["min_duration"])).strftime("%H:%M")
                            })
    
    return itinerary

# Find the optimal schedule
optimal_itinerary = find_optimal_schedule(start_time, travel_times, meeting_constraints)

# Output the result as JSON
result = {"itinerary": optimal_itinerary}
print(json.dumps(result, indent=2))