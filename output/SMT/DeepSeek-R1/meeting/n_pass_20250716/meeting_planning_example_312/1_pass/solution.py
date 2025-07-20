import itertools
import z3

def main():
    # Define travel times between districts
    travel_times = {
        "Richmond District": {
            "Sunset District": 11,
            "Haight-Ashbury": 10,
            "Mission District": 20,
            "Golden Gate Park": 9
        },
        "Sunset District": {
            "Richmond District": 12,
            "Haight-Ashbury": 15,
            "Mission District": 24,
            "Golden Gate Park": 11
        },
        "Haight-Ashbury": {
            "Richmond District": 10,
            "Sunset District": 15,
            "Mission District": 11,
            "Golden Gate Park": 7
        },
        "Mission District": {
            "Richmond District": 20,
            "Sunset District": 24,
            "Haight-Ashbury": 12,
            "Golden Gate Park": 17
        },
        "Golden Gate Park": {
            "Richmond District": 7,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Mission District": 17
        }
    }
    
    friends = ['Sarah', 'Richard', 'Elizabeth', 'Michelle']
    
    locations_map = {
        'Sarah': 'Sunset District',
        'Richard': 'Haight-Ashbury',
        'Elizabeth': 'Mission District',
        'Michelle': 'Golden Gate Park'
    }
    
    availability_map = {
        'Sarah': (105, 600),    # 10:45 AM to 7:00 PM
        'Richard': (165, 405),   # 11:45 AM to 3:45 PM
        'Elizabeth': (120, 495), # 11:00 AM to 5:15 PM
        'Michelle': (555, 705)   # 6:15 PM to 8:45 PM
    }
    
    duration_map = {
        'Sarah': 30,
        'Richard': 90,
        'Elizabeth': 120,
        'Michelle': 90
    }
    
    # Try subsets from largest to smallest (4 down to 0)
    found_schedule = None
    found_perm = None
    for subset_size in range(4, -1, -1):
        for subset in itertools.combinations(friends, subset_size):
            for perm in itertools.permutations(subset):
                solver = z3.Solver()
                start_times = [z3.Int(f'start_{i}') for i in range(len(perm))]
                constraints = []
                current_location = "Richmond District"
                current_time = 0
                
                for i, friend in enumerate(perm):
                    loc = locations_map[friend]
                    travel_time = travel_times[current_location][loc]
                    s_i = start_times[i]
                    available_start, available_end = availability_map[friend]
                    duration_val = duration_map[friend]
                    
                    constraints.append(s_i >= current_time + travel_time)
                    constraints.append(s_i >= available_start)
                    constraints.append(s_i + duration_val <= available_end)
                    
                    current_time = s_i + duration_val
                    current_location = loc
                
                solver.add(constraints)
                if solver.check() == z3.sat:
                    model = solver.model()
                    schedule_details = []
                    for i, friend in enumerate(perm):
                        s_val = model.eval(start_times[i]).as_long()
                        total_minutes = s_val
                        hours = total_minutes // 60
                        minutes = total_minutes % 60
                        total_hours = 9 + hours
                        hour_12 = total_hours % 12
                        if hour_12 == 0:
                            hour_12 = 12
                        period = "AM" if total_hours < 12 else "PM"
                        time_str = f"{hour_12}:{minutes:02d} {period}"
                        
                        end_val = s_val + duration_map[friend]
                        end_hours = 9 + (end_val // 60)
                        end_minutes = end_val % 60
                        end_hour_12 = end_hours % 12
                        if end_hour_12 == 0:
                            end_hour_12 = 12
                        end_period = "AM" if end_hours < 12 else "PM"
                        end_time_str = f"{end_hour_12}:{end_minutes:02d} {end_period}"
                        
                        schedule_details.append((friend, time_str, end_time_str))
                    
                    found_schedule = schedule_details
                    found_perm = perm
                    break
            if found_schedule is not None:
                break
        if found_schedule is not None:
            break
    
    if found_schedule is not None:
        print(f"We can meet {len(found_perm)} friends: {', '.join(found_perm)}")
        print("Detailed schedule:")
        for i, (friend, start_str, end_str) in enumerate(found_schedule):
            location = locations_map[friend]
            print(f"  {i+1}. Meet {friend} at {location} from {start_str} to {end_str}")
    else:
        print("We can meet 0 friends.")

if __name__ == '__main__':
    main()