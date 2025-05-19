import json
from datetime import datetime, timedelta

# Meeting constraints and travel times
arrival_time = datetime.strptime('9:00', '%H:%M')
emily_start = datetime.strptime('16:00', '%H:%M')
emily_end = datetime.strptime('17:15', '%H:%M')
margaret_start = datetime.strptime('19:00', '%H:%M')
margaret_end = datetime.strptime('21:00', '%H:%M')

required_emily_duration = timedelta(minutes=45)
required_margaret_duration = timedelta(minutes=120)

# Travel distances in minutes
travel_times = {
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Russian Hill"): 4,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Russian Hill"): 13,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 11,
}

def calculate_meeting_schedule():
    itinerary = []

    # First, meeting Emily at Union Square
    travel_to_emily = travel_times[("North Beach", "Union Square")]
    meet_start = max(arrival_time + timedelta(minutes=travel_to_emily), emily_start)
    meet_end = meet_start + required_emily_duration

    if meet_end <= emily_end:
        itinerary.append({
            "action": "meet",
            "location": "Union Square",
            "person": "Emily",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": meet_end.strftime("%H:%M")
        })

        # Travel to Margaret at Russian Hill
        travel_to_margaret = travel_times[("Union Square", "Russian Hill")]
        departure_to_margaret = meet_end + timedelta(minutes=travel_to_margaret)

        # Meeting Margaret at Russian Hill
        if departure_to_margaret < margaret_start:
            departure_to_margaret = margaret_start  # Wait if necessary

        meet_start_margaret = departure_to_margaret
        meet_end_margaret = meet_start_margaret + required_margaret_duration
        
        if meet_end_margaret <= margaret_end:
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": meet_start_margaret.strftime("%H:%M"),
                "end_time": meet_end_margaret.strftime("%H:%M")
            })

    return {"itinerary": itinerary}

# Calculate and output the optimal meeting schedule
optimal_schedule = calculate_meeting_schedule()
output_json = json.dumps(optimal_schedule, indent=2)
print(output_json)