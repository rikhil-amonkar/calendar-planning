import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Mission District'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Mission District'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Pacific Heights'): 16
    }
    
    current_location = 'Nob Hill'
    current_time = parse_time("9:00")
    
    thomas_available_start = parse_time("15:30")
    thomas_available_end = parse_time("19:15")
    thomas_min_duration = 75  # minutes
    
    kenneth_available_start = parse_time("12:00")
    kenneth_available_end = parse_time("15:45")
    kenneth_min_duration = 45  # minutes
    
    itinerary = []
    
    # Try to meet Kenneth first
    # Calculate travel time to Mission District
    travel_to_kenneth = travel_times[(current_location, 'Mission District')]
    arrival_at_kenneth = current_time + timedelta(minutes=travel_to_kenneth)
    
    # Check if we can meet Kenneth
    if arrival_at_kenneth <= kenneth_available_end - timedelta(minutes=kenneth_min_duration):
        # Determine meeting start time (max of arrival and Kenneth's available start)
        meet_kenneth_start = max(arrival_at_kenneth, kenneth_available_start)
        meet_kenneth_end = meet_kenneth_start + timedelta(minutes=kenneth_min_duration)
        
        if meet_kenneth_end <= kenneth_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Kenneth",
                "start_time": format_time(meet_kenneth_start),
                "end_time": format_time(meet_kenneth_end)
            })
            
            # Update current time and location after meeting Kenneth
            current_time = meet_kenneth_end
            current_location = 'Mission District'
            
            # Now try to meet Thomas
            travel_to_thomas = travel_times[(current_location, 'Pacific Heights')]
            arrival_at_thomas = current_time + timedelta(minutes=travel_to_thomas)
            
            if arrival_at_thomas <= thomas_available_end - timedelta(minutes=thomas_min_duration):
                meet_thomas_start = max(arrival_at_thomas, thomas_available_start)
                meet_thomas_end = meet_thomas_start + timedelta(minutes=thomas_min_duration)
                
                if meet_thomas_end <= thomas_available_end:
                    itinerary.append({
                        "action": "meet",
                        "location": "Pacific Heights",
                        "person": "Thomas",
                        "start_time": format_time(meet_thomas_start),
                        "end_time": format_time(meet_thomas_end)
                    })
                    return {"itinerary": itinerary}
    
    # If meeting Kenneth first didn't work, try meeting Thomas first
    itinerary = []
    current_location = 'Nob Hill'
    current_time = parse_time("9:00")
    
    # Calculate travel time to Pacific Heights
    travel_to_thomas = travel_times[(current_location, 'Pacific Heights')]
    arrival_at_thomas = current_time + timedelta(minutes=travel_to_thomas)
    
    # Check if we can meet Thomas now (but he's only available after 15:30)
    if arrival_at_thomas <= thomas_available_end - timedelta(minutes=thomas_min_duration):
        meet_thomas_start = max(arrival_at_thomas, thomas_available_start)
        meet_thomas_end = meet_thomas_start + timedelta(minutes=thomas_min_duration)
        
        if meet_thomas_end <= thomas_available_end:
            # But meeting Thomas first would make us miss Kenneth entirely
            # So this path is invalid
            pass
    
    # If neither path works, try to meet just one person
    # Try to meet Kenneth
    itinerary = []
    current_location = 'Nob Hill'
    current_time = parse_time("9:00")
    
    travel_to_kenneth = travel_times[(current_location, 'Mission District')]
    arrival_at_kenneth = current_time + timedelta(minutes=travel_to_kenneth)
    
    if arrival_at_kenneth <= kenneth_available_end - timedelta(minutes=kenneth_min_duration):
        meet_kenneth_start = max(arrival_at_kenneth, kenneth_available_start)
        meet_kenneth_end = meet_kenneth_start + timedelta(minutes=kenneth_min_duration)
        
        if meet_kenneth_end <= kenneth_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Kenneth",
                "start_time": format_time(meet_kenneth_start),
                "end_time": format_time(meet_kenneth_end)
            })
            return {"itinerary": itinerary}
    
    # If meeting Kenneth didn't work, try meeting Thomas
    itinerary = []
    current_location = 'Nob Hill'
    current_time = parse_time("9:00")
    
    travel_to_thomas = travel_times[(current_location, 'Pacific Heights')]
    arrival_at_thomas = current_time + timedelta(minutes=travel_to_thomas)
    
    if arrival_at_thomas <= thomas_available_end - timedelta(minutes=thomas_min_duration):
        meet_thomas_start = max(arrival_at_thomas, thomas_available_start)
        meet_thomas_end = meet_thomas_start + timedelta(minutes=thomas_min_duration)
        
        if meet_thomas_end <= thomas_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Thomas",
                "start_time": format_time(meet_thomas_start),
                "end_time": format_time(meet_thomas_end)
            })
            return {"itinerary": itinerary}
    
    # If nothing works, return empty itinerary
    return {"itinerary": []}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))