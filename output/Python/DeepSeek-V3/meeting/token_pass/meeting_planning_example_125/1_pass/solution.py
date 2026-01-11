import json
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times in minutes: from_index to to_index
    locations = ["Embarcadero", "Financial District", "Alamo Square"]
    travel = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17,
    }
    
    # Start at Embarcadero at 9:00
    current_time = time_to_minutes("9:00")
    current_location = "Embarcadero"
    
    # Friend data: (name, location, available_start, available_end, min_duration_minutes)
    friends = [
        ("Stephanie", "Financial District", time_to_minutes("8:15"), time_to_minutes("11:30"), 90),
        ("John", "Alamo Square", time_to_minutes("10:15"), time_to_minutes("20:45"), 30),
    ]
    
    itinerary = []
    
    # Try to meet Stephanie first
    # Travel to Financial District
    travel_time = travel[(current_location, "Financial District")]
    arrival = current_time + travel_time
    # Start meeting as soon as possible after arrival, but within friend's window
    start_meet = max(arrival, friends[0][2])  # Stephanie's available start
    end_meet = start_meet + friends[0][4]
    if end_meet <= friends[0][3]:  # within her available end
        itinerary.append({
            "action": "meet",
            "location": friends[0][1],
            "person": friends[0][0],
            "start_time": minutes_to_time(start_meet),
            "end_time": minutes_to_time(end_meet)
        })
        # Now go to John
        travel_time2 = travel[(friends[0][1], "Alamo Square")]
        arrival2 = end_meet + travel_time2
        start_meet2 = max(arrival2, friends[1][2])
        end_meet2 = start_meet2 + friends[1][4]
        if end_meet2 <= friends[1][3]:
            itinerary.append({
                "action": "meet",
                "location": friends[1][1],
                "person": friends[1][0],
                "start_time": minutes_to_time(start_meet2),
                "end_time": minutes_to_time(end_meet2)
            })
    
    # If Stephanie-first fails, try John-first
    if len(itinerary) < 2:
        itinerary = []
        current_time = time_to_minutes("9:00")
        current_location = "Embarcadero"
        # Travel to Alamo Square first
        travel_time = travel[(current_location, "Alamo Square")]
        arrival = current_time + travel_time
        start_meet = max(arrival, friends[1][2])
        end_meet = start_meet + friends[1][4]
        if end_meet <= friends[1][3]:
            itinerary.append({
                "action": "meet",
                "location": friends[1][1],
                "person": friends[1][0],
                "start_time": minutes_to_time(start_meet),
                "end_time": minutes_to_time(end_meet)
            })
            # Now go to Stephanie
            travel_time2 = travel[(friends[1][1], "Financial District")]
            arrival2 = end_meet + travel_time2
            start_meet2 = max(arrival2, friends[0][2])
            end_meet2 = start_meet2 + friends[0][4]
            if end_meet2 <= friends[0][3]:
                itinerary.append({
                    "action": "meet",
                    "location": friends[0][1],
                    "person": friends[0][0],
                    "start_time": minutes_to_time(start_meet2),
                    "end_time": minutes_to_time(end_meet2)
                })
    
    # Output result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()