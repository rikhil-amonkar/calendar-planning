import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_time = {
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Sunset District'): 25,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Sunset District'): 15
    }
    
    friends = [
        {"name": "Ronald", "location": "Nob Hill", "available_start": 600, "available_end": 1020, "min_duration": 105},
        {"name": "Margaret", "location": "Haight-Ashbury", "available_start": 615, "available_end": 1320, "min_duration": 60},
        {"name": "Helen", "location": "The Castro", "available_start": 810, "available_end": 1020, "min_duration": 120},
        {"name": "Joshua", "location": "Sunset District", "available_start": 855, "available_end": 1170, "min_duration": 90}
    ]
    
    best_schedule = []
    best_finish_time = None
    best_n = -1
    
    n_list = [4, 3, 2, 1, 0]
    
    for n in n_list:
        for subset in itertools.combinations(friends, n):
            for perm in itertools.permutations(subset):
                current_time = 540
                current_location = "Pacific Heights"
                schedule = []
                valid = True
                for friend in perm:
                    key = (current_location, friend["location"])
                    if key not in travel_time:
                        valid = False
                        break
                    travel_duration = travel_time[key]
                    arrival_time = current_time + travel_duration
                    start_meeting = max(arrival_time, friend["available_start"])
                    if start_meeting > friend["available_end"] - friend["min_duration"]:
                        valid = False
                        break
                    end_meeting = start_meeting + friend["min_duration"]
                    if end_meeting > friend["available_end"]:
                        valid = False
                        break
                    schedule.append({
                        "action": "meet",
                        "location": friend["location"],
                        "person": friend["name"],
                        "start_time": minutes_to_time(start_meeting),
                        "end_time": minutes_to_time(end_meeting)
                    })
                    current_time = end_meeting
                    current_location = friend["location"]
                if valid:
                    finish_time = current_time
                    if n > best_n:
                        best_schedule = schedule
                        best_finish_time = finish_time
                        best_n = n
                    elif n == best_n and (best_finish_time is None or finish_time < best_finish_time):
                        best_schedule = schedule
                        best_finish_time = finish_time
                        best_n = n
        if best_n == 4:
            break
    
    result = {"itinerary": best_schedule}
    print(json.dumps(result))

if __name__ == '__main__':
    main()