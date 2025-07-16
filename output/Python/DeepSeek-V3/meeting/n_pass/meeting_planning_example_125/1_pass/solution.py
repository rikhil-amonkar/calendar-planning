import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    dt = datetime.strptime(time_str, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Travel times in minutes
    travel_times = {
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Alamo Square'): 17,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Financial District'): 17
    }

    # Constraints
    current_location = 'Embarcadero'
    current_time = time_to_minutes("9:00")
    
    stephanie_available_start = time_to_minutes("8:15")
    stephanie_available_end = time_to_minutes("11:30")
    stephanie_min_duration = 90
    stephanie_location = 'Financial District'
    
    john_available_start = time_to_minutes("10:15")
    john_available_end = time_to_minutes("20:45")
    john_min_duration = 30
    john_location = 'Alamo Square'
    
    itinerary = []
    
    # Try to meet Stephanie first
    travel_to_stephanie = travel_times[(current_location, stephanie_location)]
    arrival_stephanie = current_time + travel_to_stephanie
    
    # Calculate possible meeting window with Stephanie
    meeting_start_stephanie = max(arrival_stephanie, stephanie_available_start)
    meeting_end_stephanie = min(meeting_start_stephanie + stephanie_min_duration, stephanie_available_end)
    
    if meeting_end_stephanie - meeting_start_stephanie >= stephanie_min_duration:
        itinerary.append({
            "action": "meet",
            "location": stephanie_location,
            "person": "Stephanie",
            "start_time": minutes_to_time(meeting_start_stephanie),
            "end_time": minutes_to_time(meeting_end_stephanie)
        })
        
        # After meeting Stephanie, try to meet John
        current_time_after_stephanie = meeting_end_stephanie
        current_location_after_stephanie = stephanie_location
        
        travel_to_john = travel_times[(current_location_after_stephanie, john_location)]
        arrival_john = current_time_after_stephanie + travel_to_john
        
        meeting_start_john = max(arrival_john, john_available_start)
        meeting_end_john = min(meeting_start_john + john_min_duration, john_available_end)
        
        if meeting_end_john - meeting_start_john >= john_min_duration:
            itinerary.append({
                "action": "meet",
                "location": john_location,
                "person": "John",
                "start_time": minutes_to_time(meeting_start_john),
                "end_time": minutes_to_time(meeting_end_john)
            })
    
    else:
        # If can't meet Stephanie, try to meet John directly
        travel_to_john = travel_times[(current_location, john_location)]
        arrival_john = current_time + travel_to_john
        
        meeting_start_john = max(arrival_john, john_available_start)
        meeting_end_john = min(meeting_start_john + john_min_duration, john_available_end)
        
        if meeting_end_john - meeting_start_john >= john_min_duration:
            itinerary.append({
                "action": "meet",
                "location": john_location,
                "person": "John",
                "start_time": minutes_to_time(meeting_start_john),
                "end_time": minutes_to_time(meeting_end_john)
            })
    
    return {"itinerary": itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))