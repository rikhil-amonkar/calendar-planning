import itertools
from z3 import *

def main():
    # Build travel_time_dict from given data
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

    n_friends = len(friends)
    all_indices = list(range(n_friends))

    # Try to find a feasible schedule for a subset of friends
    schedule_found = False
    result_schedule = []
    for n in range(n_friends, 0, -1):
        for subset in itertools.combinations(all_indices, n):
            s = Solver()
            size = len(subset)
            order = [Int(f'order_{i}') for i in range(size)]
            s.add(Distinct(order))
            for i in range(size):
                s.add(Or([order[i] == j for j in subset]))
            
            start_times = [Real(f'start_{j}') for j in subset]
            start_map = {j: start_times[i] for i, j in enumerate(subset)}
            
            # Constraints for the first meeting
            first_friend = order[0]
            loc0 = friends[first_friend][1]
            travel0 = travel_time_dict[('Presidio', loc0)]
            s.add(start_map[first_friend] >= travel0)
            s.add(start_map[first_friend] >= friends[first_friend][2])
            s.add(start_map[first_friend] + friends[first_friend][4] <= friends[first_friend][3])
            
            # Constraints for subsequent meetings
            for k in range(1, size):
                prev_friend = order[k-1]
                curr_friend = order[k]
                loc_prev = friends[prev_friend][1]
                loc_curr = friends[curr_friend][1]
                travel_time_k = travel_time_dict[(loc_prev, loc_curr)]
                s.add(start_map[curr_friend] >= start_map[prev_friend] + friends[prev_friend][4] + travel_time_k)
                s.add(start_map[curr_friend] >= friends[curr_friend][2])
                s.add(start_map[curr_friend] + friends[curr_friend][4] <= friends[curr_friend][3])
            
            if s.check() == sat:
                model = s.model()
                order_vals = [model.evaluate(order[i]).as_long() for i in range(size)]
                start_vals = [model.evaluate(start_map[j]) for j in subset]
                itinerary = []
                for i in range(size):
                    friend_idx = order_vals[i]
                    start_minutes = start_vals[i]
                    if is_rational_value(start_minutes):
                        start_minutes = float(start_minutes.numerator_as_long()) / float(start_minutes.denominator_as_long())
                    else:
                        start_minutes = start_minutes.as_long()
                    start_minutes = round(start_minutes)
                    duration = friends[friend_idx][4]
                    end_minutes = start_minutes + duration
                    name = friends[friend_idx][0]
                    start_time = minutes_to_time(start_minutes)
                    end_time = minutes_to_time(end_minutes)
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_time,
                        "end_time": end_time
                    })
                result_schedule = itinerary
                schedule_found = True
                break
        if schedule_found:
            break

    if not schedule_found:
        print("No feasible schedule found.")
        result_schedule = []

    output = {"itinerary": result_schedule}
    print("SOLUTION:")
    print(output)

def is_rational_value(val):
    return is_rational(val)

def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{int(hours):02d}:{int(minutes):02d}"

if __name__ == '__main__':
    main()