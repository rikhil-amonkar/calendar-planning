import json

def main():
    # Define travel times as a nested dictionary
    travel_times = {
        'Russian Hill': {'Nob Hill': 5, 'Mission District': 16, 'Embarcadero': 8},
        'Nob Hill': {'Russian Hill': 5, 'Mission District': 13, 'Embarcadero': 9},
        'Mission District': {'Russian Hill': 15, 'Nob Hill': 12, 'Embarcadero': 19},
        'Embarcadero': {'Russian Hill': 8, 'Nob Hill': 10, 'Mission District': 20}
    }
    
    # Convert all times to minutes since 9:00 AM (which is 0 minutes)
    # Patricia: 6:30 PM to 9:45 PM -> 18:30 to 21:45 -> 570 to 765 minutes
    # Ashley: 8:30 PM to 9:15 PM -> 20:30 to 21:15 -> 690 to 735 minutes
    # Timothy: 9:45 AM to 5:45 PM -> 9:45 to 17:45 -> 45 to 525 minutes
    
    # Start at Russian Hill at time 0
    current_time = 0
    current_location = 'Russian Hill'
    itinerary = []
    
    # First, meet Timothy at Embarcadero
    travel_time_to_timothy = travel_times[current_location]['Embarcadero']
    arrival_at_embarcadero = current_time + travel_time_to_timothy
    # Wait until Timothy is available at 45 minutes (9:45 AM)
    meet_timothy_start = max(arrival_at_embarcadero, 45)
    meet_timothy_end = meet_timothy_start + 120  # 120 minutes meeting
    # Check if meeting Timothy is feasible within his availability
    if meet_timothy_end <= 525:
        itinerary.append({
            'action': 'meet',
            'location': 'Embarcadero',
            'person': 'Timothy',
            'start_time': minutes_to_time(meet_timothy_start),
            'end_time': minutes_to_time(meet_timothy_end)
        })
        current_time = meet_timothy_end
        current_location = 'Embarcadero'
    else:
        # If we can't meet Timothy, skip (but in this case we can)
        pass
    
    # Next, meet Patricia at Nob Hill
    travel_time_to_patricia = travel_times[current_location]['Nob Hill']
    arrival_at_nob_hill = current_time + travel_time_to_patricia
    # Patricia is available from 570 minutes (6:30 PM)
    # We need to leave Nob Hill by (690 - travel_time_to_ashley) to reach Ashley on time
    travel_time_to_ashley = travel_times['Nob Hill']['Mission District']
    latest_departure_from_patricia = 690 - travel_time_to_ashley
    meet_patricia_start = max(arrival_at_nob_hill, 570)
    meet_patricia_end = min(meet_patricia_start + 90, latest_departure_from_patricia)
    # Ensure we meet for at least 90 minutes
    if meet_patricia_end - meet_patricia_start >= 90:
        itinerary.append({
            'action': 'meet',
            'location': 'Nob Hill',
            'person': 'Patricia',
            'start_time': minutes_to_time(meet_patricia_start),
            'end_time': minutes_to_time(meet_patricia_end)
        })
        current_time = meet_patricia_end
        current_location = 'Nob Hill'
    else:
        # If we can't meet Patricia for 90 minutes, skip (but we can)
        pass
    
    # Finally, meet Ashley at Mission District
    travel_time_to_ashley = travel_times[current_location]['Mission District']
    arrival_at_mission = current_time + travel_time_to_ashley
    meet_ashley_start = max(arrival_at_mission, 690)
    meet_ashley_end = meet_ashley_start + 45
    # Check if meeting Ashley is feasible within her availability
    if meet_ashley_end <= 735:
        itinerary.append({
            'action': 'meet',
            'location': 'Mission District',
            'person': 'Ashley',
            'start_time': minutes_to_time(meet_ashley_start),
            'end_time': minutes_to_time(meet_ashley_end)
        })
    
    # Output the itinerary as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

def minutes_to_time(minutes_since_900):
    total_minutes = minutes_since_900
    hours = total_minutes // 60
    minutes = total_minutes % 60
    time_hour = 9 + hours
    return f"{time_hour}:{minutes:02d}"

if __name__ == '__main__':
    main()