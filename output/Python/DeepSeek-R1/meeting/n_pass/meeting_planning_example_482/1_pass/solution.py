import itertools
import json

def main():
    # Convert time to minutes from midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1][:2])  # Handle possible AM/PM by taking first two digits
        return hour * 60 + minute

    # Format minutes back to "H:MM"
    def format_minutes(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours}:{minutes:02d}"

    # Build travel time dictionary
    travel_data = [
        ('Haight-Ashbury', 'Mission District', 11),
        ('Haight-Ashbury', 'Bayview', 18),
        ('Haight-Ashbury', 'Pacific Heights', 12),
        ('Haight-Ashbury', 'Russian Hill', 17),
        ('Haight-Ashbury', "Fisherman's Wharf", 23),
        ('Mission District', 'Haight-Ashbury', 12),
        ('Mission District', 'Bayview', 15),
        ('Mission District', 'Pacific Heights', 16),
        ('Mission District', 'Russian Hill', 15),
        ('Mission District', "Fisherman's Wharf", 22),
        ('Bayview', 'Haight-Ashbury', 19),
        ('Bayview', 'Mission District', 13),
        ('Bayview', 'Pacific Heights', 23),
        ('Bayview', 'Russian Hill', 23),
        ('Bayview', "Fisherman's Wharf", 25),
        ('Pacific Heights', 'Haight-Ashbury', 11),
        ('Pacific Heights', 'Mission District', 15),
        ('Pacific Heights', 'Bayview', 22),
        ('Pacific Heights', 'Russian Hill', 7),
        ('Pacific Heights', "Fisherman's Wharf", 13),
        ('Russian Hill', 'Haight-Ashbury', 17),
        ('Russian Hill', 'Mission District', 16),
        ('Russian Hill', 'Bayview', 23),
        ('Russian Hill', 'Pacific Heights', 7),
        ('Russian Hill', "Fisherman's Wharf", 7),
        ("Fisherman's Wharf", 'Haight-Ashbury', 22),
        ("Fisherman's Wharf", 'Mission District', 22),
        ("Fisherman's Wharf", 'Bayview', 26),
        ("Fisherman's Wharf", 'Pacific Heights', 12),
        ("Fisherman's Wharf", 'Russian Hill', 7)
    ]
    
    travel_times = {}
    for loc1, loc2, time in travel_data:
        if loc1 not in travel_times:
            travel_times[loc1] = {}
        travel_times[loc1][loc2] = time

    # Define friends with constraints in minutes
    friends = [
        ('Stephanie', 'Mission District', 8*60+15, 13*60+45, 90),  # 8:15AM to 1:45PM -> 495 to 825 minutes
        ('Sandra', 'Bayview', 13*60+0, 19*60+30, 15),              # 1:00PM to 7:30PM -> 780 to 1170
        ('Brian', 'Russian Hill', 12*60+15, 16*60+0, 120),          # 12:15PM to 4:00PM -> 735 to 960
        ('Jason', "Fisherman's Wharf", 8*60+30, 17*60+45, 60)      # 8:30AM to 5:45PM -> 510 to 1065
    ]
    
    start_time_minutes = 9 * 60  # 9:00 AM
    start_location = 'Haight-Ashbury'
    
    best_count = 0
    best_itinerary = None
    
    for perm in itertools.permutations(friends):
        current_location = start_location
        current_time = start_time_minutes
        itinerary_perm = []
        
        for friend in perm:
            name, loc, avail_start, avail_end, min_dur = friend
            
            # Travel to friend's location
            tt = travel_times[current_location][loc]
            current_time += tt
            
            # Calculate meeting start and end
            start_meeting = max(current_time, avail_start)
            end_meeting = start_meeting + min_dur
            
            # Check if meeting is possible
            if end_meeting <= avail_end:
                itinerary_perm.append({
                    'person': name,
                    'location': loc,
                    'start_meeting': start_meeting,
                    'end_meeting': end_meeting
                })
                current_time = end_meeting  # Update time after meeting
            else:
                # Skip meeting, but still update location
                pass
            current_location = loc  # Update current location
        
        if len(itinerary_perm) > best_count:
            best_count = len(itinerary_perm)
            best_itinerary = itinerary_perm
            if best_count == 4:
                break  # Found optimal schedule
    
    # Convert to output format
    output_itinerary = []
    if best_itinerary:
        for meeting in best_itinerary:
            output_itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": format_minutes(meeting['start_meeting']),
                "end_time": format_minutes(meeting['end_meeting'])
            })
    
    # Output as JSON
    result = {"itinerary": output_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()