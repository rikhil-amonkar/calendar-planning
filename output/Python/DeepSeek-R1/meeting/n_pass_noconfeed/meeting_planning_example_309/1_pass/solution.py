import itertools
import json

def minutes_to_time(m):
    total_minutes = m
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    constraints = {
        'Nancy': {'location': 'CT', 'start_avail': 30, 'end_avail': 270, 'min_dur': 90},
        'Mary': {'location': 'AS', 'start_avail': 0, 'end_avail': 720, 'min_dur': 75},
        'Jessica': {'location': 'BV', 'start_avail': 135, 'end_avail': 285, 'min_dur': 45}
    }
    
    travel_times = {
        'FD': {'CT': 5, 'AS': 17, 'BV': 19, 'FW': 10},
        'CT': {'FD': 5, 'AS': 17, 'BV': 22, 'FW': 8},
        'AS': {'FD': 17, 'CT': 16, 'BV': 16, 'FW': 19},
        'BV': {'FD': 19, 'CT': 18, 'AS': 16, 'FW': 25},
        'FW': {'FD': 11, 'CT': 12, 'AS': 20, 'BV': 26}
    }
    
    location_names = {
        'FD': 'Financial District',
        'CT': 'Chinatown',
        'AS': 'Alamo Square',
        'BV': 'Bayview',
        'FW': 'Fisherman\'s Wharf'
    }
    
    friends = ['Nancy', 'Mary', 'Jessica']
    
    best_schedule = None
    max_met = -1
    
    for num in range(len(friends), 0, -1):
        for subset in itertools.combinations(friends, num):
            for order in itertools.permutations(subset):
                current_location = 'FD'
                current_time = 0
                schedule = []
                valid = True
                for friend in order:
                    loc = constraints[friend]['location']
                    travel_duration = travel_times[current_location][loc]
                    current_time += travel_duration
                    start_avail = constraints[friend]['start_avail']
                    end_avail = constraints[friend]['end_avail']
                    min_dur = constraints[friend]['min_dur']
                    
                    start_meeting = max(current_time, start_avail)
                    if start_meeting + min_dur > end_avail:
                        valid = False
                        break
                    end_meeting = start_meeting + min_dur
                    schedule.append({
                        'friend': friend,
                        'location': loc,
                        'start': start_meeting,
                        'end': end_meeting
                    })
                    current_time = end_meeting
                    current_location = loc
                
                if valid:
                    if len(subset) > max_met:
                        best_schedule = schedule
                        max_met = len(subset)
                    break
            if best_schedule is not None:
                break
        if best_schedule is not None:
            break
    
    itinerary = []
    if best_schedule is not None:
        for event in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": location_names[event['location']],
                "person": event['friend'],
                "start_time": minutes_to_time(event['start']),
                "end_time": minutes_to_time(event['end'])
            })
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()