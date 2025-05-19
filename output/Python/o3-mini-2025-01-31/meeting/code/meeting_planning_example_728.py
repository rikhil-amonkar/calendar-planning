#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    # converts integer minutes from midnight to "H:MM" format (24-hour, no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define initial starting point and start time
    current_location = "Marina District"
    # 9:00 AM in minutes after midnight
    current_time = 9 * 60  # 540
    
    # Define meeting constraints for each friend:
    # Each entry: person: {location, available_start, available_end, duration_minutes}
    meetings = {
        "Elizabeth": {"location": "Financial District", "available_start": 10*60, "available_end": 12*60 + 45, "duration": 75},
        "Joseph": {"location": "Union Square", "available_start": 11*60 + 45, "available_end": 14*60 + 45, "duration": 120},
        "Kimberly": {"location": "Haight-Ashbury", "available_start": 14*60 + 15, "available_end": 17*60 + 30, "duration": 105},
        "Richard": {"location": "Fisherman's Wharf", "available_start": 14*60 + 30, "available_end": 17*60 + 30, "duration": 30},
        "Karen": {"location": "Mission District", "available_start": 14*60 + 15, "available_end": 22*60, "duration": 30},
        "Helen": {"location": "Sunset District", "available_start": 14*60 + 45, "available_end": 20*60 + 45, "duration": 105},
        "Ashley": {"location": "Russian Hill", "available_start": 11*60 + 30, "available_end": 21*60 + 30, "duration": 45},
        "Robert": {"location": "Presidio", "available_start": 21*60 + 45, "available_end": 22*60 + 45, "duration": 60}
    }
    
    # Define the travel times we will use along our planned route as given (in minutes)
    travel_times = {
        ("Marina District", "Financial District"): 17,
        ("Financial District", "Union Square"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Mission District", "Sunset District"): 24,
        ("Sunset District", "Russian Hill"): 24,
        ("Russian Hill", "Presidio"): 14
    }
    
    itinerary = []
    
    # 1. Travel from Marina District to Financial District for Elizabeth
    travel = travel_times[(current_location, meetings["Elizabeth"]["location"])]
    current_time += travel  # travel time
    # Wait if arriving before available start
    start_meet = max(current_time, meetings["Elizabeth"]["available_start"])
    end_meet = start_meet + meetings["Elizabeth"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Elizabeth"]["location"],
        "person": "Elizabeth",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Elizabeth"]["location"]
    
    # 2. Travel to Union Square for Joseph (from Financial District)
    travel = travel_times[(current_location, meetings["Joseph"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Joseph"]["available_start"])
    end_meet = start_meet + meetings["Joseph"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Joseph"]["location"],
        "person": "Joseph",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Joseph"]["location"]
    
    # 3. Travel to Haight-Ashbury for Kimberly (from Union Square)
    travel = travel_times[(current_location, meetings["Kimberly"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Kimberly"]["available_start"])
    end_meet = start_meet + meetings["Kimberly"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Kimberly"]["location"],
        "person": "Kimberly",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Kimberly"]["location"]
    
    # 4. Travel to Fisherman's Wharf for Richard (from Haight-Ashbury)
    travel = travel_times[(current_location, meetings["Richard"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Richard"]["available_start"])
    end_meet = start_meet + meetings["Richard"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Richard"]["location"],
        "person": "Richard",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Richard"]["location"]
    
    # 5. Travel to Mission District for Karen (from Fisherman's Wharf)
    travel = travel_times[(current_location, meetings["Karen"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Karen"]["available_start"])
    end_meet = start_meet + meetings["Karen"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Karen"]["location"],
        "person": "Karen",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Karen"]["location"]
    
    # 6. Travel to Sunset District for Helen (from Mission District)
    travel = travel_times[(current_location, meetings["Helen"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Helen"]["available_start"])
    end_meet = start_meet + meetings["Helen"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Helen"]["location"],
        "person": "Helen",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Helen"]["location"]
    
    # 7. Travel to Russian Hill for Ashley (from Sunset District)
    travel = travel_times[(current_location, meetings["Ashley"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Ashley"]["available_start"])
    end_meet = start_meet + meetings["Ashley"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Ashley"]["location"],
        "person": "Ashley",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Ashley"]["location"]
    
    # 8. Travel to Presidio for Robert (from Russian Hill)
    travel = travel_times[(current_location, meetings["Robert"]["location"])]
    current_time += travel
    start_meet = max(current_time, meetings["Robert"]["available_start"])
    end_meet = start_meet + meetings["Robert"]["duration"]
    itinerary.append({
        "action": "meet",
        "location": meetings["Robert"]["location"],
        "person": "Robert",
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    })
    current_time = end_meet
    current_location = meetings["Robert"]["location"]
    
    # Build final schedule as JSON dictionary
    schedule = {"itinerary": itinerary}
    print(json.dumps(schedule, indent=2))
    
if __name__ == '__main__':
    main()