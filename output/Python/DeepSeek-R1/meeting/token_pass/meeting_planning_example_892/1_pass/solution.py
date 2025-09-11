import itertools
import json

def main():
    # Travel times dictionary
    travel_times = {
        'Marina District': {'Bayview': 27, 'Sunset District': 19, 'Richmond District': 11, 'Nob Hill': 12, 'Chinatown': 15, 'Haight-Ashbury': 16, 'North Beach': 11, 'Russian Hill': 8, 'Embarcadero': 14},
        'Bayview': {'Marina District': 27, 'Sunset District': 23, 'Richmond District': 25, 'Nob Hill': 20, 'Chinatown': 19, 'Haight-Ashbury': 19, 'North Beach': 22, 'Russian Hill': 23, 'Embarcadero': 19},
        'Sunset District': {'Marina District': 21, 'Bayview': 22, 'Richmond District': 12, 'Nob Hill': 27, 'Chinatown': 30, 'Haight-Ashbury': 15, 'North Beach': 28, 'Russian Hill': 24, 'Embarcadero': 30},
        'Richmond District': {'Marina District': 9, 'Bayview': 27, 'Sunset District': 11, 'Nob Hill': 17, 'Chinatown': 20, 'Haight-Ashbury': 10, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19},
        'Nob Hill': {'Marina District': 11, 'Bayview': 19, 'Sunset District': 24, 'Richmond District': 14, 'Chinatown': 6, 'Haight-Ashbury': 13, 'North Beach': 8, 'Russian Hill': 5, 'Embarcadero': 9},
        'Chinatown': {'Marina District': 12, 'Bayview': 20, 'Sunset District': 29, 'Richmond District': 20, 'Nob Hill': 9, 'Haight-Ashbury': 19, 'North Beach': 3, 'Russian Hill': 7, 'Embarcadero': 5},
        'Haight-Ashbury': {'Marina District': 17, 'Bayview': 18, 'Sunset District': 15, 'Richmond District': 10, 'Nob Hill': 15, 'Chinatown': 19, 'North Beach': 19, 'Russian Hill': 17, 'Embarcadero': 20},
        'North Beach': {'Marina District': 9, 'Bayview': 25, 'Sunset District': 27, 'Richmond District': 18, 'Nob Hill': 7, 'Chinatown': 6, 'Haight-Ashbury': 18, 'Russian Hill': 4, 'Embarcadero': 6},
        'Russian Hill': {'Marina District': 7, 'Bayview': 23, 'Sunset District': 23, 'Richmond District': 14, 'Nob Hill': 5, 'Chinatown': 9, 'Haight-Ashbury': 17, 'North Beach': 5, 'Embarcadero': 8},
        'Embarcadero': {'Marina District': 12, 'Bayview': 21, 'Sunset District': 30, 'Richmond District': 21, 'Nob Hill': 10, 'Chinatown': 7, 'Haight-Ashbury': 21, 'North Beach': 5, 'Russian Hill': 8}
    }
    
    # Friend data: (name, location, available_start_min, available_end_min, min_duration)
    friends = [
        ('Charles', 'Bayview', 690, 870, 45),
        ('Robert', 'Sunset District', 1005, 1260, 30),
        ('Karen', 'Richmond District', 1095, 1290, 60),
        ('Rebecca', 'Nob Hill', 975, 1230, 90),
        ('Margaret', 'Chinatown', 855, 1185, 120),
        ('Patricia', 'Haight-Ashbury', 870, 1230, 45),
        ('Mark', 'North Beach', 840, 1110, 105),
        ('Melissa', 'Russian Hill', 780, 1185, 30),
        ('Laura', 'Embarcadero', 465, 795, 105)
    ]
    
    # Generate all permutations of friends
    best_count = 0
    best_schedule = None
    start_time = 540  # 9:00 in minutes
    
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_loc = 'Marina District'
        meetings = []
        count = 0
        
        for friend in perm:
            name, loc, avail_start, avail_end, dur = friend
            travel = travel_times[current_loc][loc]
            arrival = current_time + travel
            start_meeting = max(arrival, avail_start)
            end_meeting = start_meeting + dur
            
            if end_meeting <= avail_end:
                meetings.append((name, loc, start_meeting, end_meeting))
                current_time = end_meeting
                current_loc = loc
                count += 1
        
        if count > best_count:
            best_count = count
            best_schedule = meetings
    
    # Convert best schedule to JSON format
    itinerary = []
    for meeting in best_schedule:
        name, loc, start, end = meeting
        # Convert minutes to time string
        start_str = f"{start//60}:{start%60:02d}".replace(':00', '').replace(':0', ':')
        end_str = f"{end//60}:{end%60:02d}".replace(':00', '').replace(':0', ':')
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": start_str,
            "end_time": end_str
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()