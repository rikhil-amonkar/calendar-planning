import json

def main():
    # Define travel times in minutes
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23
    }
    
    # Convert times to minutes since midnight
    kenneth_start = 12 * 60  # 12:00 PM
    kenneth_end = 15 * 60    # 3:00 PM
    barbara_start = 8 * 60 + 15  # 8:15 AM
    barbara_end = 19 * 60        # 7:00 PM
    
    kenneth_min_duration = 90  # minutes
    barbara_min_duration = 45  # minutes
    
    start_location = 'Financial District'
    start_time = 9 * 60  # 9:00 AM
    
    # Try both orders: Kenneth first, then Barbara
    solutions = []
    
    # Option 1: Kenneth first, then Barbara
    # Travel to Kenneth
    travel_to_kenneth = travel_times[(start_location, 'Chinatown')]
    earliest_kenneth_start = max(start_time + travel_to_kenneth, kenneth_start)
    
    if earliest_kenneth_start <= kenneth_end - kenneth_min_duration:
        kenneth_meeting_end = earliest_kenneth_start + kenneth_min_duration
        
        # Travel to Barbara
        travel_to_barbara = travel_times[('Chinatown', 'Golden Gate Park')]
        earliest_barbara_start = max(kenneth_meeting_end + travel_to_barbara, barbara_start)
        
        if earliest_barbara_start <= barbara_end - barbara_min_duration:
            barbara_meeting_end = earliest_barbara_start + barbara_min_duration
            total_time = kenneth_min_duration + barbara_min_duration
            solutions.append({
                'order': 'kenneth_first',
                'kenneth_start': earliest_kenneth_start,
                'kenneth_duration': kenneth_min_duration,
                'barbara_start': earliest_barbara_start,
                'barbara_duration': barbara_min_duration,
                'total_time': total_time
            })
    
    # Option 2: Barbara first, then Kenneth
    # Travel to Barbara
    travel_to_barbara = travel_times[(start_location, 'Golden Gate Park')]
    earliest_barbara_start = max(start_time + travel_to_barbara, barbara_start)
    
    if earliest_barbara_start <= barbara_end - barbara_min_duration:
        barbara_meeting_end = earliest_barbara_start + barbara_min_duration
        
        # Travel to Kenneth
        travel_to_kenneth = travel_times[('Golden Gate Park', 'Chinatown')]
        earliest_kenneth_start = max(barbara_meeting_end + travel_to_kenneth, kenneth_start)
        
        if earliest_kenneth_start <= kenneth_end - kenneth_min_duration:
            kenneth_meeting_end = earliest_kenneth_start + kenneth_min_duration
            total_time = kenneth_min_duration + barbara_min_duration
            solutions.append({
                'order': 'barbara_first',
                'kenneth_start': earliest_kenneth_start,
                'kenneth_duration': kenneth_min_duration,
                'barbara_start': earliest_barbara_start,
                'barbara_duration': barbara_min_duration,
                'total_time': total_time
            })
    
    # If we found solutions with both meetings, pick the one with earliest finish time
    if solutions:
        # Sort by total meeting time (could also sort by finish time)
        solutions.sort(key=lambda x: x['total_time'], reverse=True)
        best_solution = solutions[0]
        
        itinerary = []
        if best_solution['order'] == 'kenneth_first':
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(best_solution['kenneth_start']),
                "end_time": format_time(best_solution['kenneth_start'] + best_solution['kenneth_duration'])
            })
            itinerary.append({
                "action": "meet", 
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": format_time(best_solution['barbara_start']),
                "end_time": format_time(best_solution['barbara_start'] + best_solution['barbara_duration'])
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park", 
                "person": "Barbara",
                "start_time": format_time(best_solution['barbara_start']),
                "end_time": format_time(best_solution['barbara_start'] + best_solution['barbara_duration'])
            })
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth", 
                "start_time": format_time(best_solution['kenneth_start']),
                "end_time": format_time(best_solution['kenneth_start'] + best_solution['kenneth_duration'])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
        return
    
    # If no solution with both meetings, try to meet at least one person
    itinerary = []
    
    # Try to meet Barbara (she has longer availability)
    barbara_meeting_start = max(start_time + travel_times[('Financial District', 'Golden Gate Park')], barbara_start)
    barbara_meeting_end = barbara_meeting_start + barbara_min_duration
    
    if barbara_meeting_end <= barbara_end:
        itinerary.append({
            "action": "meet",
            "location": "Golden Gate Park", 
            "person": "Barbara",
            "start_time": format_time(barbara_meeting_start),
            "end_time": format_time(barbara_meeting_end)
        })
    
    # Try to meet Kenneth if time permits after Barbara
    if itinerary:
        last_meeting_end = barbara_meeting_end
        travel_to_kenneth = travel_times[('Golden Gate Park', 'Chinatown')]
        kenneth_arrival = last_meeting_end + travel_to_kenneth
        kenneth_meeting_start = max(kenneth_arrival, kenneth_start)
        kenneth_meeting_end = kenneth_meeting_start + kenneth_min_duration
        
        if kenneth_meeting_end <= kenneth_end:
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth", 
                "start_time": format_time(kenneth_meeting_start),
                "end_time": format_time(kenneth_meeting_end)
            })
    else:
        # If couldn't meet Barbara, try to meet Kenneth
        kenneth_meeting_start = max(start_time + travel_times[('Financial District', 'Chinatown')], kenneth_start)
        kenneth_meeting_end = kenneth_meeting_start + kenneth_min_duration
        
        if kenneth_meeting_end <= kenneth_end:
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(kenneth_meeting_start),
                "end_time": format_time(kenneth_meeting_end)
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

def format_time(minutes):
    """Convert minutes since midnight to time string in format 'H:MM AM/PM'"""
    hours = minutes // 60
    mins = minutes % 60
    
    if hours < 12:
        period = "AM"
        if hours == 0:
            hours = 12
    else:
        period = "PM"
        if hours > 12:
            hours -= 12
    
    return f"{hours}:{mins:02d} {period}"

if __name__ == "__main__":
    main()