import itertools
import json
from z3 import *

def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{int(hours):02d}:{int(minutes):02d}"

def main():
    travel_time_dict = {
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Richmond District"): 11,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Richmond District"): 21,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Richmond District"): 20,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Richmond District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Richmond District"): 21,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Richmond District"): 20,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Chinatown"): 20
    }

    friends = [
        ("Jeffrey", "Fisherman's Wharf", 75, 240, 90),
        ("Ronald", "Alamo Square", -75, 345, 120),
        ("Jason", "Financial District", 105, 420, 105),
        ("Melissa", "Union Square", 525, 555, 15),
        ("Elizabeth", "Sunset District", 345, 510, 105),
        ("Margaret", "Embarcadero", 255, 600, 90),
        ("George", "Golden Gate Park", 600, 780, 75),
        ("Richard", "Chinatown", 30, 720, 15),
        ("Laura", "Richmond District", 45, 540, 60)
    ]

    names = [f[0] for f in friends]
    locations = [f[1] for f in friends]
    available_starts = [f[2] for f in friends]
    available_ends = [f[3] for f in friends]
    min_durations = [f[4] for f in friends]

    n_friends = len(friends)
    all_indices = list(range(n_friends))
    
    schedule_found = False
    result_schedule = []
    for n in range(n_friends, 0, -1):
        for subset in itertools.combinations(all_indices, n):
            size = len(subset)
            sub_names = [names[i] for i in subset]
            sub_locations = [locations[i] for i in subset]
            sub_starts = [available_starts[i] for i in subset]
            sub_ends = [available_ends[i] for i in subset]
            sub_durations = [min_durations[i] for i in subset]
            
            travel_matrix = []
            for i in subset:
                from_loc = locations[i]
                row = []
                for j in subset:
                    to_loc = locations[j]
                    if from_loc == to_loc:
                        row.append(0)
                    else:
                        key = (from_loc, to_loc)
                        row.append(travel_time_dict[key])
                travel_matrix.append(row)
            
            travel_from_presidio = []
            for loc in sub_locations:
                key = ('Presidio', loc)
                travel_from_presidio.append(travel_time_dict[key])
            
            s = Solver()
            order = [Int(f'order_{i}') for i in range(size)]
            for i in range(size):
                s.add(order[i] >= 0, order[i] < size)
            s.add(Distinct(order))
            
            start_times = [Int(f'start_{i}') for i in range(size)]
            
            # Constraints for the first meeting
            travel0_expr = IntVal(0)
            for idx in range(size):
                travel0_expr = If(order[0] == idx, travel_from_presidio[idx], travel0_expr)
            s.add(start_times[0] >= travel0_expr)
            
            avail_start0_expr = IntVal(0)
            for idx in range(size):
                avail_start0_expr = If(order[0] == idx, sub_starts[idx], avail_start0_expr)
            s.add(start_times[0] >= avail_start0_expr)
            
            dur0_expr = IntVal(0)
            for idx in range(size):
                dur0_expr = If(order[0] == idx, sub_durations[idx], dur0_expr)
            avail_end0_expr = IntVal(0)
            for idx in range(size):
                avail_end0_expr = If(order[0] == idx, sub_ends[idx], avail_end0_expr)
            s.add(start_times[0] + dur0_expr <= avail_end0_expr)
            
            for k in range(1, size):
                prev_index = order[k-1]
                curr_index = order[k]
                
                travel_expr = IntVal(0)
                for i in range(size):
                    for j in range(size):
                        cond = And(prev_index == i, curr_index == j)
                        travel_expr = If(cond, travel_matrix[i][j], travel_expr)
                
                dur_prev_expr = IntVal(0)
                for idx in range(size):
                    dur_prev_expr = If(prev_index == idx, sub_durations[idx], dur_prev_expr)
                
                s.add(start_times[k] >= start_times[k-1] + dur_prev_expr + travel_expr)
                
                avail_start_expr = IntVal(0)
                for idx in range(size):
                    avail_start_expr = If(curr_index == idx, sub_starts[idx], avail_start_expr)
                s.add(start_times[k] >= avail_start_expr)
                
                dur_curr_expr = IntVal(0)
                for idx in range(size):
                    dur_curr_expr = If(curr_index == idx, sub_durations[idx], dur_curr_expr)
                avail_end_expr = IntVal(0)
                for idx in range(size):
                    avail_end_expr = If(curr_index == idx, sub_ends[idx], avail_end_expr)
                s.add(start_times[k] + dur_curr_expr <= avail_end_expr)
            
            if s.check() == sat:
                model = s.model()
                order_vals = [model.evaluate(order[i]).as_long() for i in range(size)]
                start_vals = [model.evaluate(start_times[i]).as_long() for i in range(size)]
                
                itinerary = []
                for i in range(size):
                    pos_in_subset = order_vals[i]
                    orig_idx = subset[pos_in_subset]
                    name = names[orig_idx]
                    start_min = start_vals[i]
                    duration = min_durations[orig_idx]
                    end_min = start_min + duration
                    start_str = minutes_to_time(start_min)
                    end_str = minutes_to_time(end_min)
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_str,
                        "end_time": end_str
                    })
                
                result_schedule = itinerary
                schedule_found = True
                break
        
        if schedule_found:
            break
    
    if not schedule_found:
        result_schedule = []
    
    output = {"itinerary": result_schedule}
    print("SOLUTION:")
    print(json.dumps(output))

if __name__ == "__main__":
    main()