import itertools
import json

def main():
    # Define the travel time matrix (10x10)
    travel_matrix = [
        [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],    # Russian Hill
        [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],   # Marina District
        [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],   # Financial District
        [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],     # Alamo Square
        [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],    # Golden Gate Park
        [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],    # The Castro
        [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],  # Bayview
        [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],  # Sunset District
        [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],     # Haight-Ashbury
        [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]     # Nob Hill
    ]
    
    # Mapping of location names to indices
    location_to_index = {
        'Russian Hill': 0,
        'Marina District': 1,
        'Financial District': 2,
        'Alamo Square': 3,
        'Golden Gate Park': 4,
        'The Castro': 5,
        'Bayview': 6,
        'Sunset District': 7,
        'Haight-Ashbury': 8,
        'Nob Hill': 9
    }
    
    # Meetings data: (name, location, start_available (min), end_available (min), min_duration)
    meetings = [
        ('Mark', 'Marina District', 18*60+45, 21*60, 90),
        ('Karen', 'Financial District', 9*60+30, 12*60+45, 90),
        ('Barbara', 'Alamo Square', 10*60, 19*60+30, 90),
        ('Nancy', 'Golden Gate Park', 16*60+45, 20*60, 105),
        ('David', 'The Castro', 9*60, 18*60, 120),
        ('Linda', 'Bayview', 18*60+15, 19*60+45, 45),
        ('Kevin', 'Sunset District', 10*60, 17*60+45, 120),
        ('Matthew', 'Haight-Ashbury', 10*60+15, 15*60+30, 45),
        ('Andrew', 'Nob Hill', 11*60+45, 16*60+45, 105)
    ]
    
    # Convert meetings to include location index
    meetings_info = []
    for meeting in meetings:
        name, loc, start, end, dur = meeting
        loc_index = location_to_index[loc]
        meetings_info.append((name, loc, loc_index, start, end, dur))
    
    n = len(meetings_info)
    best_schedule = None
    best_count = 0
    
    # Try subsets from largest to smallest
    for k in range(n, 0, -1):
        for subset in itertools.combinations(range(n), k):
            for perm in itertools.permutations(subset):
                current_time = 540  # 9:00 AM in minutes
                current_loc = 0     # Russian Hill
                schedule = []
                feasible = True
                for idx in perm:
                    name, loc_str, loc_idx, start_avail, end_avail, dur = meetings_info[idx]
                    travel_time = travel_matrix[current_loc][loc_idx]
                    arrival_time = current_time + travel_time
                    start_meeting = max(arrival_time, start_avail)
                    end_meeting = start_meeting + dur
                    if end_meeting > end_avail:
                        feasible = False
                        break
                    schedule.append((name, loc_str, start_meeting, end_meeting))
                    current_time = end_meeting
                    current_loc = loc_idx
                if feasible:
                    best_schedule = schedule
                    best_count = k
                    break
            if best_schedule is not None:
                break
        if best_schedule is not None:
            break
    
    # If no meetings can be scheduled, return empty itinerary
    if best_schedule is None:
        result = {"itinerary": []}
    else:
        itinerary = []
        for meeting in best_schedule:
            name, loc, start_min, end_min = meeting
            # Convert minutes to time string
            start_hour = start_min // 60
            start_minute = start_min % 60
            end_hour = end_min // 60
            end_minute = end_min % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
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