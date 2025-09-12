import itertools
import z3
import json

def main():
    # Travel time matrix: [Sunset District, Alamo Square, Russian Hill, Golden Gate Park, Mission District]
    travel_time = [
        [0, 17, 24, 11, 24],   # from Sunset District (index 0)
        [16, 0, 13, 9, 10],     # from Alamo Square (index 1)
        [23, 15, 0, 21, 16],    # from Russian Hill (index 2)
        [10, 10, 19, 0, 17],    # from Golden Gate Park (index 3)
        [24, 11, 15, 17, 0]     # from Mission District (index 4)
    ]
    
    location_to_index = {
        'Sunset District': 0,
        'Alamo Square': 1,
        'Russian Hill': 2,
        'Golden Gate Park': 3,
        'Mission District': 4
    }
    
    meetings = [
        {'name': 'Margaret', 'location': 'Russian Hill', 'avail_start': 0, 'avail_end': 420, 'min_dur': 30, 'loc_index': location_to_index['Russian Hill']},
        {'name': 'Daniel', 'location': 'Golden Gate Park', 'avail_start': -60, 'avail_end': 270, 'min_dur': 15, 'loc_index': location_to_index['Golden Gate Park']},
        {'name': 'Charles', 'location': 'Alamo Square', 'avail_start': 540, 'avail_end': 705, 'min_dur': 90, 'loc_index': location_to_index['Alamo Square']},
        {'name': 'Stephanie', 'location': 'Mission District', 'avail_start': 690, 'avail_end': 780, 'min_dur': 90, 'loc_index': location_to_index['Mission District']}
    ]
    
    found_schedule = None
    for k in range(4, 0, -1):
        for subset in itertools.combinations([0, 1, 2, 3], k):
            for perm in itertools.permutations(subset):
                s = z3.Solver()
                start_vars = [z3.Real(f'start_{i}') for i in range(k)]
                constraints = []
                current_time = 0
                current_loc = 0
                for i, meeting_idx in enumerate(perm):
                    meeting = meetings[meeting_idx]
                    travel = travel_time[current_loc][meeting['loc_index']]
                    constraints.append(start_vars[i] >= current_time + travel)
                    constraints.append(start_vars[i] >= meeting['avail_start'])
                    constraints.append(start_vars[i] + meeting['min_dur'] <= meeting['avail_end'])
                    current_time = start_vars[i] + meeting['min_dur']
                    current_loc = meeting['loc_index']
                
                s.add(constraints)
                if s.check() == z3.sat:
                    m = s.model()
                    start_times_minutes = []
                    for var in start_vars:
                        val = m.eval(var)
                        if z3.is_int_value(val):
                            start_times_minutes.append(int(val.as_string()))
                        else:
                            rat = val.as_fraction()
                            start_times_minutes.append(round(float(rat)))
                    
                    itinerary = []
                    for i, meeting_idx in enumerate(perm):
                        meeting = meetings[meeting_idx]
                        start_minutes = start_times_minutes[i]
                        end_minutes = start_minutes + meeting['min_dur']
                        start_hour = 9 + start_minutes // 60
                        start_minute = start_minutes % 60
                        end_hour = 9 + end_minutes // 60
                        end_minute = end_minutes % 60
                        itinerary.append({
                            "action": "meet",
                            "location": meeting['location'],
                            "person": meeting['name'],
                            "start_time": f"{start_hour}:{start_minute:02d}",
                            "end_time": f"{end_hour}:{end_minute:02d}"
                        })
                    found_schedule = itinerary
                    break
            if found_schedule is not None:
                break
        if found_schedule is not None:
            break
    
    if found_schedule is None:
        found_schedule = []
    
    result = {"itinerary": found_schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()