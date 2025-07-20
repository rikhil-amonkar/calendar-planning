import json
import itertools

def format_minutes(minutes):
    hours = minutes // 60
    minutes_remain = minutes % 60
    return f"{int(hours)}:{minutes_remain:02d}"

def main():
    # Define travel times in minutes: nested dictionary
    travel_times_dict = {
        'Golden Gate Park': {
            'Alamo Square': 10,
            'Presidio': 11,
            'Russian Hill': 19
        },
        'Alamo Square': {
            'Golden Gate Park': 9,
            'Presidio': 18,
            'Russian Hill': 13
        },
        'Presidio': {
            'Golden Gate Park': 12,
            'Alamo Square': 18,
            'Russian Hill': 14
        },
        'Russian Hill': {
            'Golden Gate Park': 21,
            'Alamo Square': 15,
            'Presidio': 14
        }
    }
    
    # Friend information
    locations = {
        'Timothy': 'Alamo Square',
        'Mark': 'Presidio',
        'Joseph': 'Russian Hill'
    }
    
    # Windows in minutes from midnight: (start, end)
    windows = {
        'Timothy': (12 * 60, 16 * 60 + 15),   # 12:00 to 16:15
        'Mark': (18 * 60 + 45, 21 * 60),       # 18:45 to 21:00
        'Joseph': (16 * 60 + 45, 21 * 60 + 30) # 16:45 to 21:30
    }
    
    # Minimum meeting times in minutes
    min_times = {
        'Timothy': 105,
        'Mark': 60,
        'Joseph': 60
    }
    
    # Start at Golden Gate Park at 9:00 AM (540 minutes)
    start_location = 'Golden Gate Park'
    start_time = 540  # 9:00 in minutes
    
    # Generate all permutations of the friends
    friends = list(locations.keys())
    permutations = list(itertools.permutations(friends))
    
    best_schedule = []
    best_count = 0
    
    for perm in permutations:
        current_location = start_location
        current_time = start_time
        schedule_perm = []
        
        for friend in perm:
            loc = locations[friend]
            travel_time = travel_times_dict[current_location][loc]
            arrival_time = current_time + travel_time
            
            window_start, window_end = windows[friend]
            min_time_val = min_times[friend]
            
            meeting_start = max(arrival_time, window_start)
            if meeting_start + min_time_val > window_end:
                break
                
            meeting_end = meeting_start + min_time_val
            schedule_perm.append((friend, loc, meeting_start, meeting_end))
            
            current_location = loc
            current_time = meeting_end
        
        count_met = len(schedule_perm)
        if count_met > best_count:
            best_count = count_met
            best_schedule = schedule_perm
            if best_count == 3:
                break
    
    # Format the best_schedule into the required JSON structure
    itinerary = []
    for meeting in best_schedule:
        friend, loc, start, end = meeting
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": friend,
            "start_time": format_minutes(start),
            "end_time": format_minutes(end)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()