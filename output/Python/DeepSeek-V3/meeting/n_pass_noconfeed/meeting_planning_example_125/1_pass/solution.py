import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Alamo Square"): 17,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Financial District"): 17,
    }

    current_location = "Embarcadero"
    current_time = parse_time("9:00")

    stephanie_window = (parse_time("8:15"), parse_time("11:30"))
    stephanie_location = "Financial District"
    stephanie_min_duration = timedelta(minutes=90)

    john_window = (parse_time("10:15"), parse_time("20:45"))
    john_location = "Alamo Square"
    john_min_duration = timedelta(minutes=30)

    itinerary = []

    # Try to meet Stephanie first
    travel_time_to_stephanie = travel_times[(current_location, stephanie_location)]
    arrival_stephanie = current_time + timedelta(minutes=travel_time_to_stephanie)
    
    # Calculate possible meeting window with Stephanie
    meeting_start_stephanie = max(arrival_stephanie, stephanie_window[0])
    meeting_end_stephanie = min(meeting_start_stephanie + stephanie_min_duration, stephanie_window[1])
    
    if meeting_end_stephanie - meeting_start_stephanie >= stephanie_min_duration:
        itinerary.append({
            "action": "meet",
            "location": stephanie_location,
            "person": "Stephanie",
            "start_time": format_time(meeting_start_stephanie),
            "end_time": format_time(meeting_end_stephanie)
        })
        
        # After meeting Stephanie, try to meet John
        travel_time_to_john = travel_times[(stephanie_location, john_location)]
        arrival_john = meeting_end_stephanie + timedelta(minutes=travel_time_to_john)
        
        meeting_start_john = max(arrival_john, john_window[0])
        meeting_end_john = min(meeting_start_john + john_min_duration, john_window[1])
        
        if meeting_end_john - meeting_start_john >= john_min_duration:
            itinerary.append({
                "action": "meet",
                "location": john_location,
                "person": "John",
                "start_time": format_time(meeting_start_john),
                "end_time": format_time(meeting_end_john)
            })
    
    # If we can't meet both, try meeting John first
    if len(itinerary) < 2:
        itinerary = []
        travel_time_to_john = travel_times[(current_location, john_location)]
        arrival_john = current_time + timedelta(minutes=travel_time_to_john)
        
        meeting_start_john = max(arrival_john, john_window[0])
        meeting_end_john = min(meeting_start_john + john_min_duration, john_window[1])
        
        if meeting_end_john - meeting_start_john >= john_min_duration:
            itinerary.append({
                "action": "meet",
                "location": john_location,
                "person": "John",
                "start_time": format_time(meeting_start_john),
                "end_time": format_time(meeting_end_john)
            })
            
            # After meeting John, try to meet Stephanie
            travel_time_to_stephanie = travel_times[(john_location, stephanie_location)]
            arrival_stephanie = meeting_end_john + timedelta(minutes=travel_time_to_stephanie)
            
            meeting_start_stephanie = max(arrival_stephanie, stephanie_window[0])
            meeting_end_stephanie = min(meeting_start_stephanie + stephanie_min_duration, stephanie_window[1])
            
            if meeting_end_stephanie - meeting_start_stephanie >= stephanie_min_duration:
                itinerary.append({
                    "action": "meet",
                    "location": stephanie_location,
                    "person": "Stephanie",
                    "start_time": format_time(meeting_start_stephanie),
                    "end_time": format_time(meeting_end_stephanie)
                })
    
    # If we still can't meet both, try meeting just Stephanie
    if len(itinerary) < 1:
        travel_time_to_stephanie = travel_times[(current_location, stephanie_location)]
        arrival_stephanie = current_time + timedelta(minutes=travel_time_to_stephanie)
        
        meeting_start_stephanie = max(arrival_stephanie, stephanie_window[0])
        meeting_end_stephanie = min(meeting_start_stephanie + stephanie_min_duration, stephanie_window[1])
        
        if meeting_end_stephanie - meeting_start_stephanie >= stephanie_min_duration:
            itinerary.append({
                "action": "meet",
                "location": stephanie_location,
                "person": "Stephanie",
                "start_time": format_time(meeting_start_stephanie),
                "end_time": format_time(meeting_end_stephanie)
            })
    
    # If we still can't meet anyone, try meeting just John
    if len(itinerary) < 1:
        travel_time_to_john = travel_times[(current_location, john_location)]
        arrival_john = current_time + timedelta(minutes=travel_time_to_john)
        
        meeting_start_john = max(arrival_john, john_window[0])
        meeting_end_john = min(meeting_start_john + john_min_duration, john_window[1])
        
        if meeting_end_john - meeting_start_john >= john_min_duration:
            itinerary.append({
                "action": "meet",
                "location": john_location,
                "person": "John",
                "start_time": format_time(meeting_start_john),
                "end_time": format_time(meeting_end_john)
            })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))