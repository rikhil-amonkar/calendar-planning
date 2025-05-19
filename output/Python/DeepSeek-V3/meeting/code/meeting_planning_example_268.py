import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def add_minutes(time_str, minutes):
    dt = parse_time(time_str)
    dt += timedelta(minutes=minutes)
    return format_time(dt)

def calculate_schedule():
    # Input parameters
    travel_times = {
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Russian Hill"): 13,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
    }

    # Constraints
    current_location = "Golden Gate Park"
    current_time = "9:00"

    timothy_constraints = {
        "location": "Alamo Square",
        "available_start": "12:00",
        "available_end": "16:15",
        "min_duration": 105
    }

    mark_constraints = {
        "location": "Presidio",
        "available_start": "18:45",
        "available_end": "21:00",
        "min_duration": 60
    }

    joseph_constraints = {
        "location": "Russian Hill",
        "available_start": "16:45",
        "available_end": "21:30",
        "min_duration": 60
    }

    itinerary = []

    # Meet Timothy at Alamo Square
    travel_time = travel_times[(current_location, timothy_constraints["location"])]
    arrival_time = add_minutes(current_time, travel_time)
    
    if parse_time(arrival_time) < parse_time(timothy_constraints["available_start"]):
        arrival_time = timothy_constraints["available_start"]
    
    end_time = add_minutes(arrival_time, timothy_constraints["min_duration"])
    if parse_time(end_time) > parse_time(timothy_constraints["available_end"]):
        end_time = timothy_constraints["available_end"]
    
    itinerary.append({
        "action": "meet",
        "location": timothy_constraints["location"],
        "person": "Timothy",
        "start_time": arrival_time,
        "end_time": end_time
    })
    
    current_location = timothy_constraints["location"]
    current_time = end_time

    # Next, decide between Joseph and Mark
    # Option 1: Meet Joseph first, then Mark
    option1_itinerary = itinerary.copy()
    option1_location = current_location
    option1_time = current_time

    # Travel to Joseph
    travel_time = travel_times[(option1_location, joseph_constraints["location"])]
    arrival_time = add_minutes(option1_time, travel_time)
    
    if parse_time(arrival_time) < parse_time(joseph_constraints["available_start"]):
        arrival_time = joseph_constraints["available_start"]
    
    end_time = add_minutes(arrival_time, joseph_constraints["min_duration"])
    if parse_time(end_time) > parse_time(joseph_constraints["available_end"]):
        end_time = joseph_constraints["available_end"]
    
    option1_itinerary.append({
        "action": "meet",
        "location": joseph_constraints["location"],
        "person": "Joseph",
        "start_time": arrival_time,
        "end_time": end_time
    })
    
    option1_location = joseph_constraints["location"]
    option1_time = end_time

    # Travel to Mark
    travel_time = travel_times[(option1_location, mark_constraints["location"])]
    arrival_time = add_minutes(option1_time, travel_time)
    
    if parse_time(arrival_time) < parse_time(mark_constraints["available_start"]):
        arrival_time = mark_constraints["available_start"]
    
    end_time = add_minutes(arrival_time, mark_constraints["min_duration"])
    if parse_time(end_time) > parse_time(mark_constraints["available_end"]):
        end_time = mark_constraints["available_end"]
    
    option1_itinerary.append({
        "action": "meet",
        "location": mark_constraints["location"],
        "person": "Mark",
        "start_time": arrival_time,
        "end_time": end_time
    })

    # Option 2: Meet Mark first, then Joseph
    option2_itinerary = itinerary.copy()
    option2_location = current_location
    option2_time = current_time

    # Travel to Mark
    travel_time = travel_times[(option2_location, mark_constraints["location"])]
    arrival_time = add_minutes(option2_time, travel_time)
    
    if parse_time(arrival_time) < parse_time(mark_constraints["available_start"]):
        arrival_time = mark_constraints["available_start"]
    
    end_time = add_minutes(arrival_time, mark_constraints["min_duration"])
    if parse_time(end_time) > parse_time(mark_constraints["available_end"]):
        end_time = mark_constraints["available_end"]
    
    option2_itinerary.append({
        "action": "meet",
        "location": mark_constraints["location"],
        "person": "Mark",
        "start_time": arrival_time,
        "end_time": end_time
    })
    
    option2_location = mark_constraints["location"]
    option2_time = end_time

    # Travel to Joseph
    travel_time = travel_times[(option2_location, joseph_constraints["location"])]
    arrival_time = add_minutes(option2_time, travel_time)
    
    if parse_time(arrival_time) < parse_time(joseph_constraints["available_start"]):
        arrival_time = joseph_constraints["available_start"]
    
    end_time = add_minutes(arrival_time, joseph_constraints["min_duration"])
    if parse_time(end_time) > parse_time(joseph_constraints["available_end"]):
        end_time = joseph_constraints["available_end"]
    
    option2_itinerary.append({
        "action": "meet",
        "location": joseph_constraints["location"],
        "person": "Joseph",
        "start_time": arrival_time,
        "end_time": end_time
    })

    # Choose the option that meets all constraints
    if len(option1_itinerary) == 3:
        return {"itinerary": option1_itinerary}
    elif len(option2_itinerary) == 3:
        return {"itinerary": option2_itinerary}
    else:
        # Fallback to meeting only Timothy and one other
        # Try meeting Timothy and Joseph
        fallback_itinerary = itinerary.copy()
        fallback_location = current_location
        fallback_time = current_time

        # Travel to Joseph
        travel_time = travel_times[(fallback_location, joseph_constraints["location"])]
        arrival_time = add_minutes(fallback_time, travel_time)
        
        if parse_time(arrival_time) < parse_time(joseph_constraints["available_start"]):
            arrival_time = joseph_constraints["available_start"]
        
        end_time = add_minutes(arrival_time, joseph_constraints["min_duration"])
        if parse_time(end_time) > parse_time(joseph_constraints["available_end"]):
            end_time = joseph_constraints["available_end"]
        
        fallback_itinerary.append({
            "action": "meet",
            "location": joseph_constraints["location"],
            "person": "Joseph",
            "start_time": arrival_time,
            "end_time": end_time
        })

        if len(fallback_itinerary) == 2:
            return {"itinerary": fallback_itinerary}
        
        # Try meeting Timothy and Mark
        fallback_itinerary = itinerary.copy()
        fallback_location = current_location
        fallback_time = current_time

        # Travel to Mark
        travel_time = travel_times[(fallback_location, mark_constraints["location"])]
        arrival_time = add_minutes(fallback_time, travel_time)
        
        if parse_time(arrival_time) < parse_time(mark_constraints["available_start"]):
            arrival_time = mark_constraints["available_start"]
        
        end_time = add_minutes(arrival_time, mark_constraints["min_duration"])
        if parse_time(end_time) > parse_time(mark_constraints["available_end"]):
            end_time = mark_constraints["available_end"]
        
        fallback_itinerary.append({
            "action": "meet",
            "location": mark_constraints["location"],
            "person": "Mark",
            "start_time": arrival_time,
            "end_time": end_time
        })

        return {"itinerary": fallback_itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))