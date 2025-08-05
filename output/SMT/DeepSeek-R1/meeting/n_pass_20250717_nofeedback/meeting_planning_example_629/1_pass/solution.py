from z3 import *
import itertools
from datetime import datetime, timedelta

def main():
    # Define travel times from the given data
    travel_data = [
        ("Russian Hill", "Presidio", 14),
        ("Russian Hill", "Chinatown", 9),
        ("Russian Hill", "Pacific Heights", 7),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "Fisherman's Wharf", 7),
        ("Russian Hill", "Golden Gate Park", 21),
        ("Russian Hill", "Bayview", 23),
        ("Presidio", "Russian Hill", 14),
        ("Presidio", "Chinatown", 21),
        ("Presidio", "Pacific Heights", 11),
        ("Presidio", "Richmond District", 7),
        ("Presidio", "Fisherman's Wharf", 19),
        ("Presidio", "Golden Gate Park", 12),
        ("Presidio", "Bayview", 31),
        ("Chinatown", "Russian Hill", 7),
        ("Chinatown", "Presidio", 19),
        ("Chinatown", "Pacific Heights", 10),
        ("Chinatown", "Richmond District", 20),
        ("Chinatown", "Fisherman's Wharf", 8),
        ("Chinatown", "Golden Gate Park", 23),
        ("Chinatown", "Bayview", 22),
        ("Pacific Heights", "Russian Hill", 7),
        ("Pacific Heights", "Presidio", 11),
        ("Pacific Heights", "Chinatown", 11),
        ("Pacific Heights", "Richmond District", 12),
        ("Pacific Heights", "Fisherman's Wharf", 13),
        ("Pacific Heights", "Golden Gate Park", 15),
        ("Pacific Heights", "Bayview", 22),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "Presidio", 7),
        ("Richmond District", "Chinatown", 20),
        ("Richmond District", "Pacific Heights", 10),
        ("Richmond District", "Fisherman's Wharf", 18),
        ("Richmond District", "Golden Gate Park", 9),
        ("Richmond District", "Bayview", 26),
        ("Fisherman's Wharf", "Russian Hill", 7),
        ("Fisherman's Wharf", "Presidio", 17),
        ("Fisherman's Wharf", "Chinatown", 12),
        ("Fisherman's Wharf", "Pacific Heights", 12),
        ("Fisherman's Wharf", "Richmond District", 18),
        ("Fisherman's Wharf", "Golden Gate Park", 25),
        ("Fisherman's Wharf", "Bayview", 26),
        ("Golden Gate Park", "Russian Hill", 19),
        ("Golden Gate Park", "Presidio", 11),
        ("Golden Gate Park", "Chinatown", 23),
        ("Golden Gate Park", "Pacific Heights", 16),
        ("Golden Gate Park", "Richmond District", 7),
        ("Golden Gate Park", "Fisherman's Wharf", 24),
        ("Golden Gate Park", "Bayview", 23),
        ("Bayview", "Russian Hill", 23),
        ("Bayview", "Presidio", 31),
        ("Bayview", "Chinatown", 18),
        ("Bayview", "Pacific Heights", 23),
        ("Bayview", "Richmond District", 25),
        ("Bayview", "Fisherman's Wharf", 25),
        ("Bayview", "Golden Gate Park", 22)
    ]
    
    travel_times = {}
    for from_loc, to_loc, time in travel_data:
        if from_loc not in travel_times:
            travel_times[from_loc] = {}
        travel_times[from_loc][to_loc] = time

    # Define friends and their constraints (name, location, start_min, end_min, duration)
    friends = [
        ("Matthew", "Presidio", 120, 720, 90),  # 11:00 AM to 9:00 PM (720)
        ("Margaret", "Chinatown", 15, 585, 90),  # 9:15 AM to 6:45 PM (585)
        ("Nancy", "Pacific Heights", 315, 480, 15),  # 2:15 PM (315) to 5:00 PM (480)
        ("Helen", "Richmond District", 645, 780, 60),  # 7:45 PM (645) to 10:00 PM (780)
        ("Rebecca", "Fisherman's Wharf", 735, 795, 60),  # 9:15 PM (735) to 10:15 PM (795)
        ("Kimberly", "Golden Gate Park", 240, 450, 120),  # 1:00 PM (240) to 4:30 PM (450)
        ("Kenneth", "Bayview", 330, 540, 60)  # 2:30 PM (330) to 6:00 PM (540)
    ]
    
    def minutes_to_time(minutes):
        base_time = datetime(2023, 1, 1, 9, 0)  # Start at 9:00 AM
        new_time = base_time + timedelta(minutes=minutes)
        return new_time.strftime("%H:%M")
    
    # First, try to schedule all 7 friends
    solver = Solver()
    s = {}
    p = {}
    for name, loc, start_min, end_min, dur in friends:
        s[name] = Real(f's_{name}')
        p[name] = Int(f'p_{name}')
        solver.add(s[name] >= start_min)
        solver.add(s[name] + dur <= end_min)
        solver.add(p[name] >= 0, p[name] < 7)
    
    solver.add(Distinct([p[name] for name, _, _, _, _ in friends]))
    
    for name, loc, _, dur, _ in friends:
        solver.add(Implies(p[name] == 0, s[name] >= travel_times["Russian Hill"][loc]))
        for other, other_loc, _, other_dur, _ in friends:
            if name == other:
                continue
            solver.add(Implies(p[name] == p[other] + 1, 
                              s[name] >= s[other] + other_dur + travel_times[other_loc][loc]))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for name, loc, start_min, end_min, dur in friends:
            start_val = model.eval(s[name])
            if is_algebraic_value(start_val):
                start_minutes = start_val.as_long()
            else:
                start_minutes = int(str(start_val))
            end_minutes = start_minutes + dur
            start_time_str = minutes_to_time(start_minutes)
            end_time_str = minutes_to_time(end_minutes)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        result = {"itinerary": itinerary_sorted}
        print("SOLUTION:")
        print(result)
        return
    
    # If all 7 not feasible, try subsets from size 7 down to 1
    all_friends = friends[:]
    found = False
    result_schedule = None
    for k in range(7, 0, -1):
        for subset in itertools.combinations(all_friends, k):
            solver = Solver()
            s = {}
            p = {}
            subset_names = [friend[0] for friend in subset]
            for name, loc, start_min, end_min, dur in subset:
                s[name] = Real(f's_{name}')
                p[name] = Int(f'p_{name}')
                solver.add(s[name] >= start_min)
                solver.add(s[name] + dur <= end_min)
                solver.add(p[name] >= 0, p[name] < k)
            
            solver.add(Distinct([p[name] for name in subset_names]))
            
            for name, loc, _, dur, _ in subset:
                solver.add(Implies(p[name] == 0, s[name] >= travel_times["Russian Hill"][loc]))
                for other, other_loc, _, other_dur, _ in subset:
                    if name == other:
                        continue
                    solver.add(Implies(p[name] == p[other] + 1, 
                                      s[name] >= s[other] + other_dur + travel_times[other_loc][loc]))
            
            if solver.check() == sat:
                model = solver.model()
                itinerary = []
                for name, loc, start_min, end_min, dur in subset:
                    start_val = model.eval(s[name])
                    if is_algebraic_value(start_val):
                        start_minutes = start_val.as_long()
                    else:
                        start_minutes = int(str(start_val))
                    end_minutes = start_minutes + dur
                    start_time_str = minutes_to_time(start_minutes)
                    end_time_str = minutes_to_time(end_minutes)
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_time_str,
                        "end_time": end_time_str
                    })
                itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
                result_schedule = {"itinerary": itinerary_sorted}
                found = True
                break
        if found:
            break
    
    if found:
        print("SOLUTION:")
        print(result_schedule)
    else:
        print("SOLUTION:")
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()